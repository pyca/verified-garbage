module

public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Primes
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Top
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86.CrtSave
import VerifiedGarbage.Proof.Bignum.X86.CrtResources

/-! # The factors' values of an RSA private key on x86: the internal function

`primes`, with `vg_rsa_private_crt`'s arguments and precondition
(`primesContract`, `Proof.Rsa.privateCrtContract`'s but for its
postcondition): it returns the low bit of the mask of `p q = n`, leaves
`R_p² mod p` (`w_p = max(2, ⌈p_len / 8⌉)` words of 32 bits, twice) in the
working space's wide slot 16 and `R_q² mod q` in 17, and changes no memory
but the working space's and the stack's below the stack pointer
(`primes_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrivPre

open VG VG.X86 VG.X86.Spill VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Bignum.X86.Crt (componentValue componentArguments)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Bignum.X86.PrivPre (primes primesBody)

/-- What `primes` leaves (see the module docs). -/
def primesPost (s t : State) : Prop :=
  t.gpr .eax = BitVec.ofNat 32 (decide (componentValue s.mem (arg s) 6 * componentValue s.mem (arg s) 8 =
    componentValue s.mem (arg s) 2)).toNat ∧
  (xIn s.mem (arg s) (arg s 3).toNat % safeM (componentValue s.mem (arg s) 6) =
      2 ^ fixB (arg s 3).toNat % safeM (componentValue s.mem (arg s) 6) →
    val32 t.mem (argumentPointer s 16) (lo (arg s 3).toNat (.slot .wide 16))
        (2 * Spec.Rsa.primeWords (arg s 7).toNat) =
      2 ^ r2Exp (arg s 7).toNat % safeM (componentValue s.mem (arg s) 6)) ∧
  (xIn s.mem (arg s) (arg s 3).toNat % safeM (componentValue s.mem (arg s) 8) =
      2 ^ fixB (arg s 3).toNat % safeM (componentValue s.mem (arg s) 8) →
    val32 t.mem (argumentPointer s 16) (lo (arg s 3).toNat (.slot .wide 17))
        (2 * Spec.Rsa.primeWords (arg s 9).toNat) =
      2 ^ r2Exp (arg s 9).toNat % safeM (componentValue s.mem (arg s) 8)) ∧
  Frame [⟨argumentPointer s 16, (arg s 17).toNat * 8⟩, below (s.gpr .esp) 96] s.mem t.mem

/-- `primes`' contract: `vg_rsa_private_crt`'s precondition and publics, and `primesPost`. -/
def primesContract : Contract isa :=
  { Proof.Rsa.privateCrtContract abi 96 with post := primesPost }

theorem primes_ok {s : State} (A : CrtABI s) :
    WP isa primes s fun t => primesPost s t ∧ abiPreserved s t := by
  have low : 48 ≤ (arg s 17).toNat * 8 := by have := A.used; omega_using [this]
  have high : (arg s 17).toNat * 8 ≤ 2 ^ 64 := by have := A.scratchBound; omega_using []
  unfold primes
  rw [entry_eq]
  refine WP.seq (WP.mono (Crt.installed_ok A) fun u ⟨I, S, K, O⟩ => ?_)
  have hI : RIn (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) u :=
    In.ofInputs I (need_le A.lengths.1 A.scratchLength)
      (by simp only [argumentPointer, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (Nat.lt_trans (arg s 16).isLt (by decide : 2 ^ 32 < 2 ^ 64))]) rfl
  refine WP.seq (WP.mono (primesBody_ok hI) fun v ⟨F, V16, V17, eax, Kv⟩ => ?_)
  have espu : u.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  have props := bodyR_props hI
  -- The registers saved at bytes 32 to 48 of the working space are kept.
  have Saved : Saved v.mem (off (argumentPointer s 16)) s.gpr Crt.savedRegisters := by
    intro p hp
    have B : 32 ≤ p.2 ∧ p.2 + 4 ≤ 48 := by
      simp only [Crt.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
    refine (F.readW (r := ⟨off (argumentPointer s 16) 32, 16⟩)
      (Offset.contains _ B.1 (by omega_using [B]) (by decide)) ?_ (by decide)).trans (S p hp)
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · rw [espu]
      have Z := I.room.apart
      rw [espu] at Z
      exact (Z.sub_right (Offset.sub_base _ (by omega_using [low]))).symm
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      rcases (props q hq).2 with h48 | h32
      · exact Offset.disjoint _ (.inl (by omega_using [h48])) (by omega_using []) (by have := (props q hq).1; omega_using [this])
      · exact Offset.disjoint _ (.inr (by omega_using [h32])) (by omega_using []) (by have := (props q hq).1; omega_using [h32])
  rw [espu] at F
  have Whole : Frame [⟨argumentPointer s 16, (arg s 17).toNat * 8⟩, below (s.gpr .esp) 96] s.mem v.mem := by
    have Start := VG.Proof.Bignum.outside_frame O (by omega_using [])
    simp only [BitVec.add_zero] at Start
    refine (Start.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)).trans
      (F.sub fun r hr => ?_)
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨_, by simp, fun _ h => h⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (props q hq).1⟩
  have Ret : v.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
    apply Whole.readW (Region.contains_self _ 4) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact A.retScratch
    · exact ret_zone40 A.stackLow
  rw [restore_eq]
  refine WP.mono (Crt.entryRestore_ok (I.scratch.of_keeps Kv (by decide) (by decide)) low Saved) fun t R => ?_
  refine ⟨?_, restored_abi R ((Kv.1 _ (by decide)).trans (K.1 _ (by decide))) Ret⟩
  have B (i : Nat) (hi : i ∈ componentArguments) :
      Spec.Rsa.bytesAt u.mem (byteAddr (arg s i)) (arg s (i + 1)).toNat =
        Spec.Rsa.bytesAt s.mem (byteAddr (arg s i)) (arg s (i + 1)).toNat := by
    apply VG.Proof.Bignum.scratch_bytes O (by have := (arg s (i + 1)).isLt; omega_using [])
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact A.nScratch
    · exact A.inScratch
    · exact A.pScratch
    · exact A.qScratch
    · exact A.dpScratch
    · exact A.dqScratch
    · exact A.qiScratch
  have cv : ∀ i ∈ componentArguments, componentValue u.mem (arg s) i = componentValue s.mem (arg s) i :=
    fun i hi => by simp only [componentValue]; rw [B i hi]
  have xi : xIn u.mem (arg s) (arg s 3).toNat = xIn s.mem (arg s) (arg s 3).toNat := by
    have e5 : (arg s 5).toNat = (arg s 3).toNat := by rw [hI.extra.inLen, BitVec.toNat_ofNat]; omega_using []
    have := B 4 (by decide)
    rw [e5] at this
    simp only [xIn]
    congr 1
    apply Mem.read_congr
    intro i hi
    have L := congrArg (fun l => l[i]?) this
    simpa [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range hi] using L
  rw [cv 2 (by decide), cv 6 (by decide), cv 8 (by decide)] at eax
  rw [xi] at V16 V17
  rw [cv 6 (by decide)] at V16
  rw [cv 8 (by decide)] at V17
  refine ⟨by rw [R.other .eax (by decide)]; exact eax, by rw [R.mem]; exact V16, by rw [R.mem]; exact V17,
    by rw [R.mem]; exact Whole⟩

end VG.Proof.Bignum.X86.PrivPre
