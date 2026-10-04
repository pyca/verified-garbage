import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.CT

/-!
# Ed448 signing with a cached public key on x86-64: `Verified`

`signCached` is verified against `signCachedContract X86_64.abi 464`:
correctness including the ABI (`signCached_wp`), constant time
(`signCached_ct`), and a state satisfying the precondition, with a public key
matching the private key, for any proof of `vg_ed448_scalar_base` (`BaseOk`,
`BaseCT`): the registration file passes its own, so that only it imports that
proof and the group theory it imports.
-/

namespace VG.Proof.Ed448.X86_64.SignCached

open VG VG.X86_64 VG.Impl.Ed448.X86_64.SignCached

/-! ## A state satisfying the precondition -/

def satSeed : List Byte := Spec.Ed448.bytesAt (fun _ => 0) 0x2000 57
def satKey : List Byte := Spec.Ed448.publicKey satSeed

theorem satKey_length : satKey.length = 57 := by
  simp only [satKey, Spec.Ed448.publicKey, Spec.Ed448.encodePoint, Spec.Ed448.encodeLE, List.length_map,
    List.length_range]

/-- The public key at `0x3000`, `scratch`'s address `0x10000` as the second
argument on the stack, and 0 elsewhere. -/
def satMem (a : Addr) : Byte :=
  if a = 0x80012 then 1 else if a.toNat < 0x3000 ∨ 0x3039 ≤ a.toNat then 0 else satKey[a.toNat - 0x3000]?.getD 0

theorem sat_seed : Spec.Ed448.bytesAt satMem 0x2000 57 = satSeed := by
  unfold satSeed Spec.Ed448.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega
  have hne : (0x2000 : Addr) + BitVec.ofNat 64 i ≠ 0x80012 := fun h => by
    have := congrArg BitVec.toNat h; rw [ha] at this; simp at this; omega
  simp only [satMem, hne, ↓reduceIte, ha, show 0x2000 + i < 0x3000 from by omega, true_or]

theorem sat_key : Spec.Ed448.bytesAt satMem 0x3000 57 = satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range, satKey_length]
  · intro i hi hj
    have hi' : i < 57 := by simpa only [Spec.Ed448.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega
    have hne : (0x3000 : Addr) + BitVec.ofNat 64 i ≠ 0x80012 := fun h => by
      have := congrArg BitVec.toNat h; rw [ha] at this; simp at this; omega
    simp only [Spec.Ed448.bytesAt, List.getElem_map, List.getElem_range, satMem, hne, ↓reduceIte, ha,
      show ¬ (0x3000 + i < 0x3000 ∨ 0x3039 ≤ 0x3000 + i) from by omega, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some]

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000
    | .r8 => 0 | .r9 => 0x5000 | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 57⟩, ⟨0x3000, 57⟩, ⟨0x4000, 0⟩, ⟨0x5000, 0⟩, ⟨0x80008, 16⟩]
  wr := [⟨0x1000, 114⟩, ⟨0x10000, 8192⟩]

theorem sat : ∃ s, (Spec.Ed448.signCachedContract X86_64.abi 464).pre s := by
  refine ⟨satState, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs, satState]
    sig_and_intros
    · decide
    · decide
    · rw [sat_seed, sat_key]
      rfl
    · decide

/-! ## `Verified` -/

theorem signCached_verified (hb : BaseOk) (hct : BaseCT) :
    Verified X86_64.target signCached (Spec.Ed448.signCachedContract X86_64.abi 464) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := signCached_wp hb h; ⟨t, s', he, ha, hq⟩, signCached_ct hb hct, sat⟩

end VG.Proof.Ed448.X86_64.SignCached
