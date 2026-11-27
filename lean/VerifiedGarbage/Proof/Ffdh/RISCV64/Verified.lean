module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Out
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Power
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Ffdh.RISCV64
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.RISCV64.CT
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_ffdh_exchange` on RISC-V: correctness

`exchange` runs the front (`front_ok`), loads and checks p (`loadP_X`), and
for a valid p computes `z = y^x mod p` (`exPre_split`) and writes it or
zeros (`exOut_split`); then it restores the registers
(`fn_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)
open VG.Impl.Dsa.RISCV64 (restore)

/-- What the branch leaves, from `s` after p's check. -/
def BrPost (x : XD) (s t : State) : Prop :=
  (Spec.Rsa.modulusValid x.p x.k = true →
    let z := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.Y x.k) ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) % x.p
    Spec.Rsa.bytesAt t.mem x.O x.k = (if 1 < z ∧ z < x.p - 1 then Spec.Rsa.i2osp z x.k else List.replicate x.k 0) ∧
      t.gpr .a0 = BitVec.ofNat 64 (if 1 < z ∧ z < x.p - 1 then 1 else 0)) ∧
  t.gpr .s6 = x.S ∧ ∃ m, Arr x s.mem m ∧ Outside x.O 0 x.k m t.mem

theorem branch_ok {x : XD} {s : State} (h : X4 x s) :
    WP isa (.ite (.zero .s0) (.seq exPre (.seq ModExp.powWinFn exOut)) (.block [.li .a0 0])) s (BrPost x s) := by
  refine WP.ite (s.gpr .s0 == 0) (Steps.eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · have hz : s.gpr .s0 = 0 := by simpa using hb
    have hv := h.2.2.mp hz
    have hf := VG.Proof.Bignum.valid_facts hv h.1.ctx.k64
    have hpk : x.p < 256 ^ x.k := by
      have := VG.Proof.Bignum.os2ip_lt (x.db.take x.k)
      rwa [take_len h.1.ctx.hL.1 h.1.ctx] at this
    unfold exPre exOut
    refine WP.seq (WP.seq (WP.mono (exPre_split h hz) fun s₁ ⟨_, h1⟩ => WP.mono h1 fun s₅ ⟨_, h5⟩ =>
      WP.seq (WP.mono h5 fun s₆ pp => ?_)))
    refine WP.seq (WP.mono (exOut_split pp.ctx pp.regs pp.p hf.1 (by rw [pp.z]; exact Nat.mod_lt _ (by omega_arith))
      hpk) fun s₇ ⟨_, h7⟩ => WP.seq (WP.mono h7 fun s₈ ⟨_, h8⟩ => WP.mono h8 fun t op => ?_))
    obtain ⟨m, am, om⟩ := op.mem
    refine ⟨fun _ => ?_, op.s6, m, pp.arr.trans am, om⟩
    rw [op.out, op.a0, pp.z]
    exact ⟨rfl, rfl⟩
  · have hz : s.gpr .s0 ≠ 0 := by simpa using hb
    refine WP.mono (WP.keep [.a0] (Q := fun t => t.mem = s.mem) (by brun [exec_li]) (by rfl) (by rfl))
      fun t ⟨tm, kt⟩ => ⟨fun hv => absurd (h.2.2.mpr hv) hz, (kt.gpr (by decide)).trans h.1.s6, t.mem,
        by rw [tm]; exact Outside.refl _ _ _ _, Outside.refl _ _ _ _⟩

theorem ret_bv (c : Prop) [Decidable c] :
    (BitVec.ofNat 64 (if c then 1 else 0)).setWidth 32 = if c then 1 else 0 := by
  split <;> rfl

theorem fn_correct (s : State) (h : fnContract.pre s) :
    ∃ tr t, Exec isa exchange s tr t ∧ abiPreserved s t ∧ fnContract.post s t := by
  show WP isa exchange s fun t => abiPreserved s t ∧ fnContract.post s t
  refine abi_of ?_
  have hpre := h
  obtain ⟨hrd, hwr, dOD, dOX, dOP, dOS, dOA, dDS, dXS, dPS, dSA, nwO, nwD, nwX, nwP, nwS, ⟨hk, hk'⟩, hL,
    hol, hpl, hx1, hxk, hsl, alS, alsp⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  have hLk : 2 * (s.gpr .a4).toNat ≤ (s.gpr .a3).toNat ∧ (s.gpr .a3).toNat ≤ 3 * (s.gpr .a4).toNat := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega_arith
  have hZ : 256 + 128 * (s.gpr .a4).toNat ≤ (stackArg s 2).toNat * 8 := by omega_arith
  have sepSO : ∀ y, ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 → (s.gpr .a1).toNat ≤ ofs (s.gpr .a0) y :=
    Pub.sep_of_disjoint dOS.symm
  rw [hol] at sepSO
  unfold exchange
  refine WP.seq (WP.mono (WP.rdwr (front_ok hpre)) fun s₃ ⟨⟨hb3, hsv, k3, o3⟩, r3, w3, _⟩ => ?_)
  refine WP.seq (WP.mono (WP.rdwr (loadP_X hb3)) fun s₄ ⟨⟨h4, a4⟩, r4, w4, _⟩ => ?_)
  refine WP.seq (WP.mono (WP.rdwr (branch_ok h4)) fun t₅ ⟨⟨tpost, t6, m, am, om⟩, r5, w5, _⟩ => ?_)
  have hc := hb3.ctx
  have hnS := hc.scr.nowrap
  change Outside (stackArg s 1) 256 ((stackArg s 2).toNat * 8 - 256) s₃.mem s₄.mem at a4
  change Outside (stackArg s 1) 256 ((stackArg s 2).toNat * 8 - 256) s₄.mem m at am
  change Outside (s.gpr .a0) 0 (s.gpr .a4).toNat m t₅.mem at om
  change (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 at hnS
  -- The saved registers' words.
  have hsav : SavedAt (stackArg s 1) t₅.mem s := fun i hi => by
    have e := ((hsv.mono a4 (Or.inr (by decide))).mono am (Or.inr (by decide))) i hi
    rw [← e]
    exact Pub.Outside.word_apart om sepSO (by omega_arith) (by omega_arith) hnS
  have hs5 : Scr t₅ (stackArg s 1) ((stackArg s 2).toNat * 8) := hc.scr.congr (by rw [w5, w4])
  refine WP.mono (restoreS_ok hs5 (by omega_arith) t6 hsav) fun u ⟨urs, u0, um⟩ => ⟨urs, ?_⟩
  · intro hdv hpv
    -- The memory apart from the working space, before the output.
    have hOZ : Outside (stackArg s 1) 0 ((stackArg s 2).toNat * 8) s.mem s₄.mem :=
      (o3.mono (Nat.le_refl _) (by omega_arith)).trans (a4.mono (by omega_arith) (by omega_arith))
    have hZx : (xdOf s).Z = (stackArg s 2).toNat * 8 := rfl
    have bY : Spec.Rsa.bytesAt s₄.mem (xdOf s).Y (xdOf s).k =
        Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat := by
      rw [show (stackArg s 0).toNat = (xdOf s).k from hpl]
      exact Pub.bytes_apart (o := 0) hOZ (by rw [hZx]; omega_arith) hc.sepY
    have bX : Spec.Rsa.bytesAt s₄.mem (xdOf s).X (xdOf s).xl =
        Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat :=
      Pub.bytes_apart (o := 0) hOZ (by rw [hZx]; omega_arith) hc.sepX
    have hmod := Proof.Ffdh.domainValid_mod hdv
    have hpe : (Spec.Ffdh.domainOf (s.gpr .a4).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)).p =
        (xdOf s).p := by
      rw [Proof.Ffdh.domainOf_p _ _ hLk.1]
      show _ = Spec.Rsa.os2ip ((Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat).take (s.gpr .a4).toNat)
      rw [Proof.Ffdh.take_bytesAt _ _ (by omega_arith)]
    rw [hpe] at hmod
    have hlo : 256 ^ ((s.gpr .a4).toNat - 1) ≤ (xdOf s).p := by
      simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, decide_eq_true_eq] at hmod; exact hmod.2
    have hpk : (xdOf s).p < 256 ^ (s.gpr .a4).toNat := by
      have := VG.Proof.Bignum.os2ip_lt ((xdOf s).db.take (xdOf s).k)
      rwa [take_len hc.hL.1 hc] at this
    obtain ⟨tb, ta⟩ := tpost hmod
    rw [bY, bX, show (xdOf s).O = s.gpr .a0 from rfl, show (xdOf s).k = (s.gpr .a4).toNat from rfl] at tb
    rw [bY, bX] at ta
    show Spec.Rsa.written u.mem (s.gpr .a0) (s.gpr .a1).toNat ((u.gpr .a0).setWidth 32) _
    rw [Proof.Ffdh.exchangeOp_eq (k := (s.gpr .a4).toNat) hpv (by rw [hpe]; exact Nat.lt_of_lt_of_le (Nat.pow_pos (by decide)) hlo)
      (by rw [hpe]; exact Proof.Ffdh.octets_bitLength (by omega_arith) hlo hpk), hpe, um, u0, ta,
      ret_bv, hol]
    generalize Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat) ^
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat) % (xdOf s).p = z at tb ⊢
    by_cases hcd : 1 < z ∧ z < (xdOf s).p - 1
    · simp only [hcd, and_self, ↓reduceIte, Spec.Rsa.written, true_and]
      rw [tb]; simp only [hcd, and_self, ↓reduceIte]
    · simp only [hcd, ↓reduceIte, Spec.Rsa.written, true_and]
      rw [tb]; simp only [hcd, ↓reduceIte]

end VG.Proof.Ffdh.RISCV64

/-!
## `vg_ffdh_exchange` on RISC-V: verified against the shared contract

`fnContract` states the shared contract on the registers and the stack
(`ex_implies`); with correctness (`fn_correct`) and constant time
(`ex_ct`), `exchange` is verified (`exchange_verified`).
-/

namespace VG.Proof.Ffdh.RISCV64

open VG VG.RISCV64

theorem stackArgs_three (s : State) :
    List.map (stackArg s) (List.range 3) = [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

/-- A state meeting `fnContract.pre`: a 512-bit p without q, `out` at
`0x1000`, the domain at `0x2000`, x at `0x3000`, the peer at `0x3100`, the
working space at `0x4000`, and the stack arguments at `0x9000`. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x2000 | .a3 => 128 | .a4 => 64 | .a5 => 0x3000 | .a6 => 1
    | .a7 => 0x3100 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9000 then 64 else bif Nat.beq a.toNat 0x9009 then 0x40 else
    bif Nat.beq a.toNat 0x9010 then 0x20 else bif Nat.beq a.toNat 0x9011 then 0x04 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x3100, 64⟩, ⟨0x9000, 24⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8448⟩]

theorem ex_implies : fnContract.Implies (Spec.Ffdh.exchangeContract RISCV64.abi) where
  pre := by
    intro s h
    sig_pre [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, RISCV64.abi, RISCV64.argRegs, fnContract,
      stackArgs_three, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
      List.append_eq, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.filterMap_cons,
      List.filterMap_nil, Sig.pairFacts, Sig.conj_cons, Sig.conj_append, List.cons_append, List.nil_append,
      List.append_nil, Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false] at h
    sig_split h
    sig_reduce [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, RISCV64.abi, RISCV64.argRegs, fnContract,
      stackArgs_three, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
      List.append_eq, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.filterMap_cons,
      List.filterMap_nil, Sig.pairFacts, Sig.conj_cons, Sig.conj_append, List.cons_append, List.nil_append,
      List.append_nil, Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | sig_disjoint_symm
      | omega
      | (sig_simp_only [Nat.mul_comm] at *
         first | with_reducible assumption | sig_disjoint_symm)
      | (simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.or_true, Bool.or_false,
          Bool.cond_true, Bool.cond_false, Sig.conj_cons, List.nil_append, List.cons_append] at *
         simp_all only [stackArgs])
  post := by
    sig_implies_post [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, RISCV64.abi, RISCV64.argRegs, fnContract,
      stackArgs_three, List.getD_cons_succ, List.getD_cons_zero]
  pub := by
    sig_implies_pub [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, RISCV64.abi, RISCV64.argRegs, fnContract,
      stackArgs_three, exLeak, List.getD_cons_succ, List.getD_cons_zero]
  sat := by
    sig_implies_sat [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, RISCV64.abi, RISCV64.argRegs, fnContract,
      stackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, Spec.Ffdh.pLenValid,
      Spec.Ffdh.domainLenValid] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

end VG.Proof.Ffdh.RISCV64

/-! ## Verified -/

namespace VG.Proof.Ffdh.RISCV64

open VG VG.RISCV64

/-- `vg_ffdh_exchange`. -/
theorem exchange_verified :
    Verified RISCV64.target Impl.Ffdh.RISCV64.exchange (Spec.Ffdh.exchangeContract RISCV64.abi 0) :=
  Verified.of_correct fn_correct ex_ct ex_implies

end VG.Proof.Ffdh.RISCV64
