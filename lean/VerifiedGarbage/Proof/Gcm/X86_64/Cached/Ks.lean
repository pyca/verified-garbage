module
public import VerifiedGarbage.Impl.Aes.X86_64.VaesZ
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
public import VerifiedGarbage.Proof.Framework.X86_64.HighKeep
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Spec

import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Gcm.X86_64.Stitch
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Rounds
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Aes

/-!
# The keys of the rounds of the blocks after the last group

What encrypting the counters of the blocks after the last group needs: the
key schedule, as the rounds need it, from a state that has not written it
(`keys_of`), and `ctrsZ` keeping the cached keys (`ctrsZ_keeps`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre nb nr kp pp cb dp dR pR cR bAddr ciph sch in_sub_int)
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Proof.Aes.X86_64.VaesZ (ctrsZ_ok four ZFrame.of_keys zmm_lane blockAt_writeW_lane)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq blockAt_frame)
open VG.Proof.Gcm.X86_64.StitchZ (AInv aregs_ok)
open VG.Spec.Gcm (Block blockAt inc32)

/-- Where the keystream goes, in the working space. -/
abbrev ksR (s₀ : State) : Region := ⟨pp s₀ + BitVec.ofNat 64 768, 256⟩

/-- The key schedule is not in the data, the working space or the counter. -/
theorem sch_frame3 {s₀ : State} (hp : SPre s₀) {m : Mem} (hf : Frame [dR s₀, pR s₀, cR s₀] s₀.mem m) :
    Spec.Aes.bytesAt m (kp s₀) (16 * (nr s₀ + 1)) = sch s₀ := by
  have hn : 16 * (nr s₀ + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> omega
  simp only [sch, Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  refine hf.bytes (R := ⟨kp s₀, 16 * (nr s₀ + 1)⟩) (fun r hr => ?_)
    (by show 16 * (nr s₀ + 1) ≤ 2 ^ 64; omega) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.d_k.symm.sub_left (Region.sub_prefix hn)
  · exact hp.p_k.symm.sub_left (Region.sub_prefix hn)
  · exact hp.c_k.symm.sub_left (Region.sub_prefix hn)

/-- The key schedule, as the rounds need it, from a state that has not
written it. -/
theorem keys_of {s₀ : State} (hp : SPre s₀) {t : State} (h1 : t.gpr .rdi = kp s₀) (h2 : t.rd = s₀.rd)
    (h3 : t.wr = s₀.wr) (h4 : Frame [dR s₀, pR s₀, cR s₀] s₀.mem t.mem) : Keys (nr s₀) (sch s₀) t :=
  ⟨by rw [h1, sch_frame3 hp h4], by rcases hp.rounds with h | h | h <;> omega,
    fun j hj => by
      rw [h2, h3, h1]
      exact Stitch.in_sub_int hp.k_in (by rcases hp.rounds with h | h | h <;> omega)⟩

theorem ctrsZ_keeps (c m i : XReg) : ∀ regs : List XReg,
    (Impl.Aes.X86_64.VaesZ.ctrsZ c m i regs).all Instr.keepsH = true
  | [] => rfl
  | _ :: bs => by
    simp only [Impl.Aes.X86_64.VaesZ.ctrsZ, List.all_append, ctrsZ_keeps c m i bs, Bool.and_true]; rfl

end VG.Proof.Gcm.X86_64.StitchZH
