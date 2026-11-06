module

public import VerifiedGarbage.Spec.Sha3.Instances
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# SHA-3 and SHAKE: each instance from the sponge

What the sponge's contracts (`Spec/Sha3/Contract.lean`) give, with an
instance's rate and suffix, in terms of the functions of FIPS 202 that the
instances' contracts (`Spec/Sha3/Instances.lean`) name: the digest is the
first bytes of the output of the padded state (`hashSponge`), the padded
state of an extendable-output function continues its output from the start
(`xofRepr_pad`), and squeezing continues it (`xofRepr_squeeze`).

On the targets whose functions keep their working space in a frame of
their own that also holds a copy of their arguments, the pre- and
postconditions must read the memory on entry only within the functions'
buffers (`finalizePost_local`, …): the state, through `stateAt`, which reads
only its 200 bytes.
-/

@[expose] public section

namespace VG.Proof.Sha3.Instances

open VG.Spec.Sha3

theorem squeezeFrom_zero (r : Nat) (S : State) (d : Nat) : squeezeFrom r S 0 d = squeeze r S d := by
  simp [squeezeFrom, squeeze]

theorem squeezeFrom_shift (r : Nat) (S : State) (pos a d : Nat) :
    squeezeFrom r S (pos + a) d = (squeezeFrom r S pos (a + d)).drop a := by
  simp only [squeezeFrom, List.drop_take, List.drop_drop]
  have e : pos + (a + d) = pos + a + d := by omega
  have e2 : a + d - a = d := by omega
  rw [e, e2]

/-- A hash function is its sponge with SHA-3's suffix (§6.1). -/
def hashSponge (H : HashFn) : Prop :=
  ∀ msg, H.digest msg = squeeze H.rate (absorb H.rate (pad H.rate sha3Suffix msg)) H.len

/-- An extendable-output function is its sponge with SHAKE's suffix (§6.2). -/
def xofSponge (X : Xof) : Prop :=
  ∀ msg d, X.xof msg d = squeeze X.rate (absorb X.rate (pad X.rate shakeSuffix msg)) d

theorem sha3_224_sponge : hashSponge hashSha3_224 := fun _ => rfl
theorem sha3_256_sponge : hashSponge hashSha3_256 := fun _ => rfl
theorem sha3_384_sponge : hashSponge hashSha3_384 := fun _ => rfl
theorem sha3_512_sponge : hashSponge hashSha3_512 := fun _ => rfl
theorem shake128_sponge : xofSponge xofShake128 := fun _ _ => rfl
theorem shake256_sponge : xofSponge xofShake256 := fun _ _ => rfl

/-- The digest, from the padded state, squeezed from position 0. -/
theorem digest_of_pad {H : HashFn} (hH : hashSponge H) {S : State} {msg : List Byte}
    (hS : S = absorb H.rate (pad H.rate sha3Suffix msg)) :
    squeezeFrom H.rate S 0 H.len = H.digest msg := by
  rw [squeezeFrom_zero, hS, hH]

/-- The padded state continues the output from its start. -/
theorem xofRepr_pad {X : Xof} (hX : xofSponge X) {mem : Mem} {p : Addr} {msg : List Byte}
    (hS : stateAt mem p = absorb X.rate (pad X.rate shakeSuffix msg)) :
    XofRepr mem p X.rate 0 X.xof msg 0 := by
  intro d
  rw [squeezeFrom_zero, hS, Nat.zero_add, List.drop_zero, hX]

/-- Squeezing `len` bytes from a state that continues the output after `n`
bytes writes the next `len`, and leaves one that continues it after
`n + len`. -/
theorem xofRepr_squeeze {rate pos ret len n : Nat} {xof : List Byte → Nat → List Byte}
    {msg out : List Byte} {m m' : Mem} {p : Addr}
    (hR : XofRepr m p rate pos xof msg n)
    (hout : out = squeezeFrom rate (stateAt m p) pos len)
    (hcont : ∀ d, squeezeFrom rate (stateAt m' p) ret d = squeezeFrom rate (stateAt m p) (pos + len) d) :
    out = (xof msg (n + len)).drop n ∧ XofRepr m' p rate ret xof msg (n + len) := by
  refine ⟨hout ▸ hR len, fun d => ?_⟩
  rw [hcont, squeezeFrom_shift, hR, List.drop_drop, Nat.add_assoc]

/-! ## Signatures with the working space as an argument -/

/-- `vg_<f>_finalize` for SHAKE with its working space passed in `scratch`. -/
def xofFinalizeScratchSig : Sig where
  params := [("state", .array true .u64 25), ("pos", .int .usize true),
    ("scratch", .array true .u64 80)]

def xofFinalizeScratchContract {M : ISA} (A : Abi M) (X : Xof) (stack : Nat := 0) : Contract M :=
  xofFinalizeScratchSig.contract A
    (pre := fun state pos _scratch => xofFinalizePre X A.ptrBits state pos)
    (post := fun state pos _scratch => xofFinalizePost X A.ptrBits state pos)
    (writeArgs := true) (stack := stack)

/-- `vg_<f>_squeeze` for SHAKE with its working space passed in `scratch`. -/
def xofSqueezeScratchSig : Sig where
  params := [("state", .array true .u64 25), ("pos", .int .usize true),
    ("out", .slice true .u8 "outlen"), ("scratch", .array true .u64 80)]
  ret := some .usize

def xofSqueezeScratchContract {M : ISA} (A : Abi M) (X : Xof) (stack : Nat := 0) : Contract M :=
  xofSqueezeScratchSig.contract A
    (pre := fun state pos out outlen _scratch => xofSqueezePre X A.ptrBits state pos out outlen)
    (post := fun state pos out outlen _scratch =>
      xofSqueezePost X A.ptrBits state pos out outlen)
    (writeArgs := true) (stack := stack)

/-- SHA-3's `vg_<f>_finalize` with its working space (`n` words) passed in
`scratch`. -/
def finScratchSig (D n : Nat) : Sig where
  params := [("state", .array true .u64 25), ("pos", .int .usize true),
    ("out", .array true .u8 D), ("scratch", .array true .u64 n)]

def finScratchContract {M : ISA} (A : Abi M) (H : HashFn) (n : Nat) (stack : Nat := 0) : Contract M :=
  (finScratchSig H.len n).contract A
    (pre := fun state pos out _scratch => finalizePre H A.ptrBits state pos out)
    (post := fun state pos out _scratch => finalizePost H A.ptrBits state pos out)
    (writeArgs := true) (stack := stack)

/-! ## Locality -/

theorem agree_of {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

theorem stateAt_agree {m₁ m₂ : Mem} {p : Addr}
    (h : ∀ a, Region.Contains ⟨p, 8 * 25⟩ a 1 → m₁ a = m₂ a) : stateAt m₂ p = stateAt m₁ p :=
  Proof.Sha3.stateAt_congr fun i hi => agree_of h i (by omega)

variable (pb : Nat)

theorem finalizePre_local (H : HashFn) : ∀ vs m₁ m₂, vs.length = ((finalizeSig H.len).words pb).length →
    (∀ b ∈ Sig.bufs (finalizeSig H.len).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply ((finalizeSig H.len).words pb) (finalizePre H pb) vs m₁ →
      Curry.apply ((finalizeSig H.len).words pb) (finalizePre H pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 2
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

theorem finalizePost_local (H : HashFn) : ∀ vs m₁ m₂ m' r,
    vs.length = ((finalizeSig H.len).words pb).length →
    (∀ b ∈ Sig.bufs (finalizeSig H.len).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply ((finalizeSig H.len).words pb) (finalizePost H pb) vs m₁ m' r →
      Curry.apply ((finalizeSig H.len).words pb) (finalizePost H pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 2
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [finalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (finalizePost H pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (finalizePost H pb) _ m₂ m' r
  dsimp only [Curry.apply, finalizePost, ArgWord.ofRaw] at h ⊢
  intro msg hr hp
  refine h msg ?_ hp
  unfold Spec.Sha3.Repr at hr ⊢
  rw [← hr]; exact (stateAt_agree hb.1).symm

theorem xofFinalizePre_local (X : Xof) : ∀ vs m₁ m₂, vs.length = (xofFinalizeSig.words pb).length →
    (∀ b ∈ Sig.bufs xofFinalizeSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (xofFinalizeSig.words pb) (xofFinalizePre X pb) vs m₁ →
      Curry.apply (xofFinalizeSig.words pb) (xofFinalizePre X pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

theorem xofFinalizePost_local (X : Xof) : ∀ vs m₁ m₂ m' r,
    vs.length = (xofFinalizeSig.words pb).length →
    (∀ b ∈ Sig.bufs xofFinalizeSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (xofFinalizeSig.words pb) (xofFinalizePost X pb) vs m₁ m' r →
      Curry.apply (xofFinalizeSig.words pb) (xofFinalizePost X pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [xofFinalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq, Elem.size] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb] (xofFinalizePost X pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb] (xofFinalizePost X pb) _ m₂ m' r
  dsimp only [Curry.apply, xofFinalizePost, ArgWord.ofRaw] at h ⊢
  intro msg hr hp
  refine h msg ?_ hp
  unfold Spec.Sha3.Repr at hr ⊢
  rw [← hr]; exact (stateAt_agree hb).symm

theorem xofSqueezePre_local (X : Xof) : ∀ vs m₁ m₂, vs.length = (xofSqueezeSig.words pb).length →
    (∀ b ∈ Sig.bufs xofSqueezeSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (xofSqueezeSig.words pb) (xofSqueezePre X pb) vs m₁ →
      Curry.apply (xofSqueezeSig.words pb) (xofSqueezePre X pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 3
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

theorem xofSqueezePost_local (X : Xof) : ∀ vs m₁ m₂ m' r,
    vs.length = (xofSqueezeSig.words pb).length →
    (∀ b ∈ Sig.bufs xofSqueezeSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (xofSqueezeSig.words pb) (xofSqueezePost X pb) vs m₁ m' r →
      Curry.apply (xofSqueezeSig.words pb) (xofSqueezePost X pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 3
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [xofSqueezeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (xofSqueezePost X pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (xofSqueezePost X pb) _ m₂ m' r
  dsimp only [Curry.apply, xofSqueezePost, ArgWord.ofRaw, XofRepr] at h ⊢
  rw [stateAt_agree (m₁ := m₁) (m₂ := m₂) hb.1]
  exact h

end VG.Proof.Sha3.Instances
