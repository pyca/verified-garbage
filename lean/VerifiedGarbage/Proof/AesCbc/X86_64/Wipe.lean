module

public import VerifiedGarbage.Proof.AesCbc.X86_64.Caller
public import VerifiedGarbage.Proof.AesCbc.X86_64.Vaes512Decrypt
public import VerifiedGarbage.Proof.Framework.X86_64.CallWipe
public import VerifiedGarbage.Proof.Zeroize.X86_64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig

/-!
# AES-CBC on x86-64, zeroing the scratch space it writes

Each implementation of `vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` that
writes its `scratch` buffer is called by `callWipe`, which then zeroes the
bytes it may write (`encWrites`, `decWrites`) with `vg_zeroize`, so that no
implementation leaves the key schedule or the data there for its caller to
wipe. The ones that write none (`vg_aes_cbc_encrypt_aesni`) are not wrapped.

`Verified.callWipe` needs the contract's postcondition to read the memory
on entry only within the buffers (`decryptPost_local`, `encryptPost_local`)
and the memory on return only within the buffers apart from `scratch`
(`decryptPost_out`, `encryptPost_out`): the key schedule (of at most 240
bytes for any schedule `Aes.KeySchedule` allows), the chaining value and the
data.
-/

@[expose] public section

namespace VG.Proof.AesCbc.X86_64.Wipe

open VG VG.X86_64 VG.Proof.Aes.X86_64 VG.Spec.Cbc

/-! ## Locality -/

section

variable {m₁ m₂ : Mem} {p : Addr}

theorem bytesAt_congr {n : Nat}
    (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on the
region. -/
theorem agree_of {n : Nat} (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

theorem blocksAt_congr {n : Nat}
    (h : ∀ i < n * 16, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    blocksAt m₂ p n = blocksAt m₁ p n := by
  simp only [blocksAt]
  refine List.map_congr_left fun j hj => bytesAt_congr fun i hi => ?_
  have hj := List.mem_range.mp hj
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by omega)

/-- A key schedule is read within the 240 bytes at `schedule`. -/
theorem keySchedule_congr {r : Nat} {key : List Byte}
    (h : ∀ i < 240, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.KeySchedule m₂ p r key ↔ Spec.Aes.KeySchedule m₁ p r key := by
  simp only [Spec.Aes.KeySchedule]
  constructor <;> rintro ⟨hl, hr, hb⟩ <;> refine ⟨hl, hr, ?_⟩ <;>
    · have : 16 * (r + 1) ≤ 240 := by
        simp only [Spec.Aes.rounds] at hr; omega
      first
      | rw [← bytesAt_congr fun i hi => h i (by omega)]; exact hb
      | rw [bytesAt_congr fun i hi => h i (by omega)]; exact hb

end

/-! ## The postconditions -/

/-- The precondition of both contracts reads no memory. -/
theorem pre_local : ∀ vs (m₁ m₂ : Mem), vs.length = (aesSig.words 64).length →
    (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesSig.words 64) (fun _schedule (rounds : BitVec 64) _iv _data _n _scratch (_ : Mem) =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) vs m₁ →
    Curry.apply (aesSig.words 64) (fun _schedule (rounds : BitVec 64) _iv _data _n _scratch (_ : Mem) =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 5) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 5
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

/-- `aesDecryptContract`'s postcondition. -/
def decPost : aesSig.Post 64 := fun schedule rounds iv data n _scratch m m' _ =>
  ∀ key, Spec.Aes.KeySchedule m schedule rounds.toNat key →
    let ciphInv := Spec.Cbc.aesInv key
    let cs := blocksAt m data n.toNat
    blocksAt m' data n.toNat = Spec.Cbc.decrypt ciphInv (Spec.Aes.bytesAt m iv 16) cs ∧
      Spec.Aes.bytesAt m' iv 16 = next (Spec.Aes.bytesAt m iv 16) cs

theorem decPost_curry (sch r iv data n scr : BitVec 64) (m m' : Mem) x :
    Curry.apply (aesSig.words 64) decPost [sch, r, iv, data, n, scr] m m' x =
      ∀ key, Spec.Aes.KeySchedule m sch r.toNat key →
        blocksAt m' data n.toNat =
            Spec.Cbc.decrypt (Spec.Cbc.aesInv key) (Spec.Aes.bytesAt m iv 16) (blocksAt m data n.toNat) ∧
          Spec.Aes.bytesAt m' iv 16 = next (Spec.Aes.bytesAt m iv 16) (blocksAt m data n.toNat) := rfl

/-- `aesEncryptContract`'s postcondition. -/
def encPost : aesSig.Post 64 := fun schedule rounds iv data n _scratch m m' _ =>
  ∀ key, Spec.Aes.KeySchedule m schedule rounds.toNat key →
    let ciph := Spec.Cbc.aes key
    let cs := Spec.Cbc.encrypt ciph (Spec.Aes.bytesAt m iv 16) (blocksAt m data n.toNat)
    blocksAt m' data n.toNat = cs ∧ Spec.Aes.bytesAt m' iv 16 = next (Spec.Aes.bytesAt m iv 16) cs

theorem encPost_curry (sch r iv data n scr : BitVec 64) (m m' : Mem) x :
    Curry.apply (aesSig.words 64) encPost [sch, r, iv, data, n, scr] m m' x =
      ∀ key, Spec.Aes.KeySchedule m sch r.toNat key →
        blocksAt m' data n.toNat =
            Spec.Cbc.encrypt (Spec.Cbc.aes key) (Spec.Aes.bytesAt m iv 16) (blocksAt m data n.toNat) ∧
          Spec.Aes.bytesAt m' iv 16 = next (Spec.Aes.bytesAt m iv 16)
            (Spec.Cbc.encrypt (Spec.Cbc.aes key) (Spec.Aes.bytesAt m iv 16) (blocksAt m data n.toNat)) :=
  rfl

theorem decPost_local : ∀ vs m₁ m₂ m' x, vs.length = (aesSig.words 64).length →
    (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesSig.words 64) decPost vs m₁ m' x → Curry.apply (aesSig.words 64) decPost vs m₂ m' x := by
  intro vs m₁ m₂ m' x hlen hb h
  obtain ⟨sch, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 5) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨r, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨scr, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  replace h := Eq.mp (decPost_curry sch r iv data n scr m₁ m' x) h
  refine Eq.mpr (decPost_curry sch r iv data n scr m₂ m' x) ?_
  intro key hk
  rw [bytesAt_congr (agree_of hb.2.1), blocksAt_congr (agree_of hb.2.2.1)]
  exact h key ((keySchedule_congr (agree_of hb.1)).mp hk)

theorem encPost_local : ∀ vs m₁ m₂ m' x, vs.length = (aesSig.words 64).length →
    (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesSig.words 64) encPost vs m₁ m' x → Curry.apply (aesSig.words 64) encPost vs m₂ m' x := by
  intro vs m₁ m₂ m' x hlen hb h
  obtain ⟨sch, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 5) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨r, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨scr, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  replace h := Eq.mp (encPost_curry sch r iv data n scr m₁ m' x) h
  refine Eq.mpr (encPost_curry sch r iv data n scr m₂ m' x) ?_
  intro key hk
  rw [bytesAt_congr (agree_of hb.2.1), blocksAt_congr (agree_of hb.2.2.1)]
  exact h key ((keySchedule_congr (agree_of hb.1)).mp hk)

theorem decPost_out : ∀ vs m m₁ m₂ x, vs.length = (aesSig.words 64).length →
    (Sig.bufs aesSig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
    (∀ b ∈ Sig.bufs aesSig.params vs, b.1.Disjoint ⟨vs.getD 5 0, 272 * Elem.u64.size⟩ →
      ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesSig.words 64) decPost vs m m₁ x → Curry.apply (aesSig.words 64) decPost vs m m₂ x := by
  intro vs m m₁ m₂ x hlen hpw hb h
  obtain ⟨sch, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 5) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨r, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨scr, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one, List.getD_cons_succ, List.getD_cons_zero] at hb
  simp only [aesSig, Sig.bufs, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one, Bool.true_or, Bool.false_or,
    List.Pairwise.nil, and_true, forall_const] at hpw
  replace h := Eq.mp (decPost_curry sch r iv data n scr m m₁ x) h
  refine Eq.mpr (decPost_curry sch r iv data n scr m m₂ x) ?_
  intro key hk
  rw [bytesAt_congr (p := iv) (agree_of (hb.2.1 hpw.2.1.2)),
    blocksAt_congr (agree_of (hb.2.2.1 hpw.2.2.1))]
  exact h key hk

theorem encPost_out : ∀ vs m m₁ m₂ x, vs.length = (aesSig.words 64).length →
    (Sig.bufs aesSig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
    (∀ b ∈ Sig.bufs aesSig.params vs, b.1.Disjoint ⟨vs.getD 5 0, 272 * Elem.u64.size⟩ →
      ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesSig.words 64) encPost vs m m₁ x → Curry.apply (aesSig.words 64) encPost vs m m₂ x := by
  intro vs m m₁ m₂ x hlen hpw hb h
  obtain ⟨sch, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 5) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨r, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨scr, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one, List.getD_cons_succ, List.getD_cons_zero] at hb
  simp only [aesSig, Sig.bufs, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one, Bool.true_or, Bool.false_or,
    List.Pairwise.nil, and_true, forall_const] at hpw
  replace h := Eq.mp (encPost_curry sch r iv data n scr m m₁ x) h
  refine Eq.mpr (encPost_curry sch r iv data n scr m m₂ x) ?_
  intro key hk
  rw [bytesAt_congr (p := iv) (agree_of (hb.2.1 hpw.2.1.2)),
    blocksAt_congr (agree_of (hb.2.2.1 hpw.2.2.1))]
  exact h key hk

/-! ## Wrapping an implementation -/

/-- A call of `name`, whose code is `body`, then of `vg_zeroize` on the first
`n` bytes of `scratch` (the sixth argument, in `r9`). -/
def wiped (n : Nat) (name : String) (body : Prog isa) : Prog isa :=
  Impl.CallWipe.X86_64.callWipe .r9 n name body "vg_zeroize" Impl.Zeroize.X86_64.zeroize

theorem wiped_spSafe {n : Nat} {name : String} {body : Prog isa}
    (h : body.all (fun i => !isa.writesSp i) = true) : (wiped n name body).all (fun i => !isa.writesSp i) = true :=
  callWipe_spSafe h (by decide)

/-- An implementation of `vg_aes_cbc_decrypt` with 8 bytes of stack, wrapped. -/
theorem wiped_decrypt {n : Nat} {name : String} {body : Prog isa}
    (h : Verified X86_64.target body (Spec.Cbc.aesDecryptContract X86_64.abi 8))
    (hsp : body.all (fun i => !isa.writesSp i) = true) (hd : body.x86_64Depth ≤ 8) (hn : n ≤ 2176) :
    Verified X86_64.target (wiped n name body) (Spec.Cbc.aesDecryptContract X86_64.abi 32) :=
  Verified.callWipe (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (i := 5)
    h Proof.Zeroize.X86_64.verified (by decide) rfl rfl rfl (by simp only [Elem.size]; omega) (by omega)
    (by decide) hsp hd (by decide) (by decide) (by omega) pre_local decPost_local decPost_out
    (by implies_sat [Spec.Cbc.aesSig, X86_64.abi, X86_64.argRegs] [Proof.AesCbc.X86_64.sat]
      using Proof.AesCbc.X86_64.sat)

/-- An implementation of `vg_aes_cbc_encrypt` with 8 bytes of stack, wrapped. -/
theorem wiped_encrypt {n : Nat} {name : String} {body : Prog isa}
    (h : Verified X86_64.target body (Spec.Cbc.aesEncryptContract X86_64.abi 8))
    (hsp : body.all (fun i => !isa.writesSp i) = true) (hd : body.x86_64Depth ≤ 8) (hn : n ≤ 2176) :
    Verified X86_64.target (wiped n name body) (Spec.Cbc.aesEncryptContract X86_64.abi 32) :=
  Verified.callWipe (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (i := 5)
    h Proof.Zeroize.X86_64.verified (by decide) rfl rfl rfl (by simp only [Elem.size]; omega) (by omega)
    (by decide) hsp hd (by decide) (by decide) (by omega) pre_local encPost_local encPost_out
    (by implies_sat [Spec.Cbc.aesSig, X86_64.abi, X86_64.argRegs] [Proof.AesCbc.X86_64.sat]
      using Proof.AesCbc.X86_64.sat)

/-! ## The implementations, wrapped -/

theorem decrypt_depth (v : BlocksImpl) : (Caller.decrypt v).x86_64Depth ≤ 8 := by
  unfold Caller.decrypt
  split
  · decide
  · split
    · decide
    · simp only [Impl.AesCbc.X86_64.decrypt, Impl.AesCbc.X86_64.batched, Impl.AesCbc.X86_64.groups,
        Impl.AesCbc.X86_64.decGroup, Impl.AesCbc.X86_64.decBody, Code.x86_64Depth, v.decNoStack]
      omega

theorem encrypt_depth (v : BlocksImpl) : (Caller.encrypt v).x86_64Depth ≤ 8 := by
  unfold Caller.encrypt
  split
  · decide
  · simp only [Impl.AesCbc.X86_64.encrypt, Impl.AesCbc.X86_64.whole, Impl.AesCbc.X86_64.encBody,
      Code.x86_64Depth, v.encNoStack]
    omega

/-- The bytes of `scratch` that `Caller.decrypt v` may write: 224 for the
loops in AES-NI or VAES registers, all of them for the others. -/
def decWrites (v : BlocksImpl) : Nat :=
  if Caller.vaes v then 224 else if Caller.hardware v then 224 else 2176

theorem decWrites_le (v : BlocksImpl) : decWrites v ≤ 2176 := by
  unfold decWrites; split
  · decide
  · split <;> decide

/-- `vg_aes_cbc_decrypt` for `v`, wrapped. -/
def decrypt (v : BlocksImpl) : Prog isa :=
  wiped (decWrites v) ("vg_aes_cbc_decrypt_unwiped" ++ v.suffix) (Caller.decrypt v)

theorem decrypt_verified (v : BlocksImpl) :
    Verified X86_64.target (decrypt v) (Spec.Cbc.aesDecryptContract X86_64.abi 32) :=
  wiped_decrypt (Proof.AesCbc.decrypt_keyed (Caller.decryptVerified v)) (Caller.decryptSpSafe v)
    (decrypt_depth v) (decWrites_le v)

theorem decrypt_spSafe (v : BlocksImpl) : (decrypt v).all (fun i => !isa.writesSp i) = true :=
  wiped_spSafe (Caller.decryptSpSafe v)

/-- `vg_aes_cbc_encrypt` for `v`, wrapped: for the baseline loop, which may
write all of `scratch` (the loop in AES-NI registers writes none of it, and
is not wrapped). -/
def encrypt (v : BlocksImpl) : Prog isa :=
  wiped 2176 ("vg_aes_cbc_encrypt_unwiped" ++ v.suffix) (Caller.encrypt v)

theorem encrypt_verified (v : BlocksImpl) :
    Verified X86_64.target (encrypt v) (Spec.Cbc.aesEncryptContract X86_64.abi 32) :=
  wiped_encrypt (Proof.AesCbc.encrypt_keyed (Caller.verified v)) (Caller.spSafe v) (encrypt_depth v)
    (by decide)

theorem encrypt_spSafe (v : BlocksImpl) : (encrypt v).all (fun i => !isa.writesSp i) = true :=
  wiped_spSafe (Caller.spSafe v)

/-- `vg_aes_cbc_decrypt_vaes_avx512`, wrapped. -/
def decryptVaes512 : Prog isa :=
  wiped 224 "vg_aes_cbc_decrypt_unwiped_vaes_avx512" Impl.AesCbc.X86_64.Vaes512Decrypt.decrypt

theorem decryptVaes512_verified :
    Verified X86_64.target decryptVaes512 (Spec.Cbc.aesDecryptContract X86_64.abi 32) :=
  wiped_decrypt (Proof.AesCbc.decrypt_keyed Vaes512Decrypt.verified) Vaes512Decrypt.spSafe (by decide)
    (by decide)

theorem decryptVaes512_spSafe : decryptVaes512.all (fun i => !isa.writesSp i) = true :=
  wiped_spSafe Vaes512Decrypt.spSafe

end VG.Proof.AesCbc.X86_64.Wipe
