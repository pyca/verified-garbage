module

import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Hdr
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Trial.Loop
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Pre
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Ctx

/-!
# DSA's probable-prime test on PPC64LE: trial division

`Tab T m`: the table `VG_RSA_KEYGEN_TRIAL32` at `T` in `m`. `trial_ok`: the
table's address (`adrSym`), its entries for the width (`hCnt`), and the loop
(`loop_ok`): `r22` is 1 exactly when trial division finds `c` composite
(`Spec.RsaKeyGen.obviouslyComposite`, `trial_spec`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime
open VG.Impl.RsaKeyGen
open VG.Impl.MillerRabin.PPC64LE.Search (ldh)
open VG.Proof.Bignum (word off slot)
open VG.Impl.Bignum (hdrBytes)
open VG.Proof.MillerRabin.PPC64LE (Env arr)

/-- The table in memory `m` at `T`. -/
def Tab (T : Addr) (m : Mem) : Prop :=
  ∀ i < 1024, m.readW (T + BitVec.ofNat 64 (8 * i)) 64 = BitVec.ofNat 64 (TrialTable32.entry i)

/-- Trial division by the width's entries is RSA's. -/
theorem trial_spec {bits c : Nat} (hb : Bits bits) (large : 8161 < c) :
    VG.Proof.RsaKeyGen.trialPrefix c (count bits) = Spec.RsaKeyGen.obviouslyComposite bits c := by
  have := VG.Proof.RsaKeyGen.trialPrefix_spec (w := words bits) large
  rw [(shape_of hb).hcount, this]
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp [Spec.RsaKeyGen.obviouslyComposite, Spec.RsaKeyGen.trialPrimes, words]

/-- The registers `trial` writes. -/
def trialRegs : List Reg := VG.Proof.RsaKeyGen.PPC64LE.Trial.entryRegs

/-- Trial division of `c` in array 0. -/
theorem trial_ok {bits c : Nat} {s : State} {B T : Addr}
    (e : Env s B (8 * keyWords bits) (words bits)) (hc : arr s.mem B (words bits) 0 = c)
    (hcnt : word s.mem B (8 * hCnt) = BitVec.ofNat 64 (count bits))
    (hT : s.syms TrialTable32.symbol = T) (htab : Tab T s.mem) (hTr : ⟨T, 8192⟩ ∈ s.rd) :
    WP isa (VG.Impl.RsaKeyGen.PPC64LE.Trial.trial hCnt) s fun t =>
      (t.gpr .r22 = BitVec.ofNat 64 (if VG.Proof.RsaKeyGen.trialPrefix c (count bits) then 1 else 0) ∧
        t.mem = s.mem) ∧ (∀ r, r ∉ trialRegs → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.syms = s.syms := by
  have hZ : 256 + 28 * (8 * (words bits + 2)) ≤ 8 * keyWords bits := e.hZ
  have hw4 := e.hw
  have hw128 := e.hw'
  have hn : 1 ≤ count bits ∧ count bits ≤ 1024 := by unfold count; split <;> decide
  have hsc := e.hs
  unfold VG.Impl.RsaKeyGen.PPC64LE.Trial.trial
  refine WP.of_syms (WP.seq (WP.mono (Q := fun (u : State) => (u.gpr .r23 = T ∧
      u.gpr .r24 = BitVec.ofNat 64 (count bits) ∧ u.mem = s.mem ∧ u.syms = s.syms) ∧ (∀ r, r ∉ trialRegs → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧
      u.wr = s.wr ∧ u.sp = s.sp)
    ?_ fun u ⟨⟨u23, u24, um, us⟩, ug, urd, uwr, usp⟩ => ?_))
  · refine WP.cons (exec_adrSym (by decide)) ?_
    simp only [ldh, hCnt]
    prun [e.h31, hsc.ld (d := 40) (n := 8) (by omega)]
    refine ⟨⟨hT, hcnt, rfl⟩, fun r hr => ?_⟩
    have h1 : r ≠ .r23 := fun h => hr (by subst h; decide)
    have h2 : r ≠ .r24 := fun h => hr (by subst h; decide)
    simp only [h1, h2, ↓reduceIte]
  · refine WP.mono (VG.Proof.RsaKeyGen.PPC64LE.Trial.loop_ok (n := count bits) (o := slot (words bits) 0) (w := words bits) (hsc.congr uwr) ?_ ?_ ?_
      (by omega) (by omega) (by simp only [slot, hdrBytes]; omega) hn.1 hn.2 u23 (fun i hi => ⟨by rw [um]; exact htab i (by omega), ?_⟩) u24)
      fun t ⟨⟨t22, tm⟩, kt⟩ sy => ⟨⟨t22, tm.trans um⟩, fun r hr => (kt.gpr r hr).trans (ug r hr),
        kt.rd.trans urd, kt.wr.trans uwr, kt.sp.trans usp, sy⟩
    · exact (ug _ (by decide)).trans e.h10
    · exact (ug _ (by decide)).trans e.h11
    · rw [um]; exact hc
    · refine ⟨_, by rw [urd]; exact List.mem_append_left _ hTr, ?_⟩
      simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]; omega

end VG.Proof.Dsa.PPC64LE.Prime
