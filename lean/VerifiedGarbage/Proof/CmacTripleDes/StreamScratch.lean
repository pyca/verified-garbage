module

public import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.Proof.CmacTripleDes.Stream
import VerifiedGarbage.Proof.CmacTripleDes.Scratch
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Streaming TDEA-CMAC with its working space as an argument

`vg_cmac_triple_des_stream_init`, `absorb` and `finish` keep their working
space in a frame of their own (`Verified.stackScratch`), around code proved
with the working space as an argument: `streamInitScratchContract`,
`absorbScratchContract` and `finishScratchContract` are the shared contracts
with a `scratch` buffer appended, whatever it holds: the 640 bytes of the
code of `init`, `update` and `finalize` they run, and for `absorb` 48 more,
where it keeps our caller's registers.

On x86 and ARMv7 the frame also holds a copy of the arguments passed on the
stack, which needs the pre- and postconditions to read the memory on entry
only within the function's buffers (`streamInitPost_local`,
`absorbPost_local`, `finishPost_local`): the key, the data, and the
streaming state, through `tdesRepr`, which reads only the state's 416 bytes
(`repr_congr_416`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream

open VG.Spec.Cmac

/-- `vg_cmac_triple_des_stream_init` with `scratch: *mut [u64; 80]`. -/
def streamInitScratchSig : Sig where
  params := [("state", .array true .u64 52), ("key", .slice false .u8 "key_len"),
    ("scratch", .array true .u64 80)]

/-- `tdesStreamInitContract`, whatever `scratch` is. -/
def streamInitScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamInitScratchSig.contract A
    (pre := fun state key keyLen _scratch => tdesStreamInitPre A.ptrBits state key keyLen)
    (post := fun state key keyLen _scratch => tdesStreamInitPost A.ptrBits state key keyLen)
    (stack := stack)

/-- `vg_cmac_triple_des_absorb` with `scratch: *mut [u64; 86]`. -/
def absorbScratchSig : Sig where
  params := [("state", .array true .u64 52), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 86)]

/-- `tdesAbsorbContract`, whatever `scratch` is. -/
def absorbScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  absorbScratchSig.contract A
    (post := fun state count data len _scratch => tdesAbsorbPost A.ptrBits state count data len)
    (stack := stack)

/-- `vg_cmac_triple_des_finish` with `scratch: *mut [u64; 80]`. -/
def finishScratchSig : Sig where
  params := [("state", .array true .u64 52), ("count", .int .u64 true),
    ("out", .array true .u8 8), ("scratch", .array true .u64 80)]

/-- `tdesFinishContract`, whatever `scratch` is. -/
def finishScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finishScratchSig.contract A
    (post := fun state count out _scratch => tdesFinishPost A.ptrBits state count out)
    (stack := stack)

/-! ## Locality -/

variable (pb : Nat)

theorem streamInitPre_local : ∀ vs m₁ m₂, vs.length = (tdesStreamInitSig.words pb).length →
    (∀ b ∈ Sig.bufs tdesStreamInitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (tdesStreamInitSig.words pb) (tdesStreamInitPre pb) vs m₁ →
      Curry.apply (tdesStreamInitSig.words pb) (tdesStreamInitPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 2
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

theorem streamInitPost_local : ∀ vs m₁ m₂ m' r, vs.length = (tdesStreamInitSig.words pb).length →
    (∀ b ∈ Sig.bufs tdesStreamInitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (tdesStreamInitSig.words pb) (tdesStreamInitPost pb) vs m₁ m' r →
      Curry.apply (tdesStreamInitSig.words pb) (tdesStreamInitPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨key, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨kl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [tdesStreamInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hk := Proof.CmacTripleDes.agree_of hb.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb] (tdesStreamInitPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb] (tdesStreamInitPost pb) _ m₂ m' r
  dsimp only [Curry.apply, tdesStreamInitPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le kl.toNat (2 ^ pb)
  rw [Proof.CmacTripleDes.tdesBytesAt_congr (n := (kl.setWidth pb).toNat) fun i hi => hk i (by
    rw [BitVec.toNat_setWidth] at hi; omega)]
  exact h

theorem absorbPost_local : ∀ vs m₁ m₂ m' r, vs.length = (tdesAbsorbSig.words pb).length →
    (∀ b ∈ Sig.bufs tdesAbsorbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (tdesAbsorbSig.words pb) (tdesAbsorbPost pb) vs m₁ m' r →
      Curry.apply (tdesAbsorbSig.words pb) (tdesAbsorbPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [tdesAbsorbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := Proof.CmacTripleDes.agree_of hb.1
  have hd := Proof.CmacTripleDes.agree_of hb.2
  change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int pb]
    (tdesAbsorbPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int pb]
    (tdesAbsorbPost pb) _ m₂ m' r
  dsimp only [Curry.apply, tdesAbsorbPost, ArgWord.ofRaw] at h ⊢
  intro key msg hr h1 h2
  have := Nat.mod_le len.toNat (2 ^ pb)
  rw [Proof.CmacTripleDes.bytesAt_congr (n := (len.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega)]
  exact h key msg (repr_congr_416 (fun i hi => (hs i (by omega)).symm) hr) h1 h2

theorem finishPost_local : ∀ vs m₁ m₂ m' r, vs.length = (tdesFinishSig.words pb).length →
    (∀ b ∈ Sig.bufs tdesFinishSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (tdesFinishSig.words pb) (tdesFinishPost pb) vs m₁ m' r →
      Curry.apply (tdesFinishSig.words pb) (tdesFinishPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 2
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [tdesFinishSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := Proof.CmacTripleDes.agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr]
    (tdesFinishPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr]
    (tdesFinishPost pb) _ m₂ m' r
  dsimp only [Curry.apply, tdesFinishPost, ArgWord.ofRaw] at h ⊢
  intro key msg hr
  exact h key msg (repr_congr_416 (fun i hi => (hs i (by omega)).symm) hr)

end VG.Proof.CmacTripleDes.Stream
