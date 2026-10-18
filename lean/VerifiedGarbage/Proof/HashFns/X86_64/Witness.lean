module

public import VerifiedGarbage.Spec.HashFns
public import VerifiedGarbage.Proof.Framework.X86_64.CallMeets
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Sha1.Md
public import VerifiedGarbage.Proof.Sha1.StateMem
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.Sig

/-!
# Functions meeting the streaming contracts (x86-64)

The precondition of a function taking a table of streaming hash functions
(`Spec.HashFns.tableOf`) can hold: in a state whose functions at the
table's addresses are `sha1Init`, `sha1Update` and `sha1Finalize`, SHA-1's
streaming functions as functions of the machine state, which change memory
only where their contracts let them, as the contracts say, and leak nothing
(`init_meets`, `update_meets`, `finalize_meets`). The contracts' witnesses
(`sat`) use them.

`meets_of` is what such a function needs: the memory it leaves, within the
writable regions (so apart from the return address), is what the contract's
postcondition asks for.
-/

@[expose] public section

namespace VG.Proof.HashFns.X86_64.Witness

open VG VG.X86_64
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha1 (md)
open VG.Proof.Sha1.StateMem (writeState stateAt_writeState)
open VG.WriteBytes (writeBytes writeBytes_before writeBytes_frame)

/-- The function that leaves the registers and changes memory to `g`, and
leaks nothing. -/
def memFn (g : Arch → Mem) : IcallFn := ⟨fun a => some ({ a with mem := g a }, []), []⟩

/-- A function that changes only the writable regions of its entry, as the
postcondition of `K` asks, meets `K` with 8 bytes of stack. -/
theorem meets_of {K : Abi isa → Nat → Contract isa} {stack : Nat} {s : State} {a : Addr} {g : Arch → Mem}
    (h : s.funs a = some (memFn g))
    (hrun : ∀ s₁, (K abi 8).pre s₁ → Frame s₁.wr s₁.mem (g s₁.arch) ∧
      (∀ r ∈ s₁.wr, r.Disjoint ⟨s₁.gpr .rsp, 8⟩) ∧ (K abi 8).post s₁ (s₁.withArch { s₁.arch with mem := g s₁.arch })) :
    FnMeets abi K 8 stack s a := by
  refine ⟨_, [], by simp only [isa, fnAt, h]; rfl, by simp only [fnConsts, h]; rfl, ?_, ?_, ?_⟩
  · simp only [abi]
    exact ⟨fun c hc => absurd hc List.not_mem_nil, fun t ht => absurd ht List.not_mem_nil⟩
  · intro s₁ _ _ hp
    obtain ⟨hF, hd, hq⟩ := hrun s₁ hp
    refine ⟨_, [], rfl, ⟨⟨fun r _ => rfl, ?_, rfl⟩, fun x hx _ => hF x hx⟩, hq⟩
    exact hF.readW (r := ⟨s₁.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => (hd r hr).symm) (by decide)
  · intro _ _ t₁ t₂ _ _ _ _ _ _ _ _ _ h₁ h₂
    simp only [memFn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    rw [← h₁.2, ← h₂.2]

/-- SHA-1's streaming functions, `HashFns.streaming 1`. -/
abbrev T : Spec.HashFns.Streaming := ⟨Spec.Hmac.sha1S, 20, 20⟩

theorem streaming_one : Spec.HashFns.streaming 1 = some T := rfl

/-- The five words of a hash value written within a region of at least 20
bytes at `p`. -/
theorem frame_writeState (m : Mem) (p : Addr) (v : Spec.Sha1.HashValue) {n : Nat} (hn : 20 ≤ n) : Frame [⟨p, n⟩] m (writeState m p v) := by
  have c : ∀ k < 5, Region.Contains ⟨p, n⟩ (p + BitVec.ofNat 64 (4 * k)) (32 / 8) := fun k hk =>
    Offset.contains_base _ (by omega) (by omega)
  have r := List.mem_singleton_self (⟨p, n⟩ : Region)
  exact (((((Frame.refl _ m).writeW r _ (c 0 (by decide))).writeW r _ (c 1 (by decide))).writeW r _
    (c 2 (by decide))).writeW r _ (c 3 (by decide))).writeW r _ (c 4 (by decide))

/-! ## `init` -/

/-- The empty message's state at `rdi`. -/
def initMem (a : Arch) : Mem := writeState a.mem (a.gpr .rdi) Spec.Sha1.H0

def sha1Init : IcallFn := memFn initMem

/-- What `init` does, from an entry its contract holds of. -/
theorem init_run : ∀ s₁ : State, (Spec.HashFns.initContract T abi 8).pre s₁ → Frame s₁.wr s₁.mem (initMem s₁.arch) ∧
    (∀ r ∈ s₁.wr, r.Disjoint ⟨s₁.gpr .rsp, 8⟩) ∧
      (Spec.HashFns.initContract T abi 8).post s₁ (s₁.withArch { s₁.arch with mem := initMem s₁.arch }) := by
  intro s₁ hp
  sig_pre [Spec.HashFns.initContract, Spec.HashFns.initSig, abi, argRegs, stackBelow] at hp
  obtain ⟨-, -, hwr, hd, -, -⟩ := hp
  refine ⟨by rw [hwr]; exact frame_writeState _ _ _ (by decide), fun r hr => ?_, ?_⟩
  · rw [hwr, List.mem_singleton] at hr; subst hr; exact hd.symm
  · unfold Spec.HashFns.initContract
    sig_reduce [Spec.HashFns.initSig, Spec.HashFns.initPost, abi, argRegs]
    exact Proof.Sha1.Stream.repr_nil (stateAt_writeState _ _ _)

theorem init_meets {stack : Nat} {s : State} {a : Addr} (h : s.funs a = some sha1Init) :
    FnMeets abi (fun A n => Spec.HashFns.initContract T A n) 8 stack s a :=
  meets_of h init_run

/-! ## Appending to a streaming state -/

/-- The state at `p` represents `m ++ d` if its hash value is the one of `m`
updated with the whole blocks of `m`'s buffered bytes followed by `d`, and
its buffer holds the rest of them. -/
theorem repr_append {B N L : Nat} (H : Proof.MdStream.Md B N L) {iv : H.HV} {mem mem' : Mem} {p : Addr}
    {m d : List Byte} (hB : 0 < B) (hr : H.Repr iv mem p m)
    (hs : H.stateAt mem' p = H.compressList (H.stateAt mem p) (m.drop (B * (m.length / B)) ++ d)
      ((m.drop (B * (m.length / B)) ++ d).length / B))
    (hb : bytesAt mem' (p + BitVec.ofNat 64 N) ((m.drop (B * (m.length / B)) ++ d).length % B) =
      (m.drop (B * (m.length / B)) ++ d).drop (B * ((m.drop (B * (m.length / B)) ++ d).length / B))) :
    H.Repr iv mem' p (m ++ d) := by
  have hle := Proof.MdStream.Md.mul_div_le m.length B
  have hx : (m.drop (B * (m.length / B)) ++ d).length = m.length - B * (m.length / B) + d.length := by simp
  have hl : (m ++ d).length = B * (m.length / B) + (m.drop (B * (m.length / B)) ++ d).length := by
    rw [hx, List.length_append]; omega
  have hdiv : (m ++ d).length / B = m.length / B + (m.drop (B * (m.length / B)) ++ d).length / B := by
    rw [hl, Nat.mul_add_div hB]
  have hmod : (m ++ d).length % B = (m.drop (B * (m.length / B)) ++ d).length % B := by
    rw [hl, Nat.mul_add_mod]
  have hdrop : (m ++ d).drop (B * (m.length / B)) = m.drop (B * (m.length / B)) ++ d :=
    List.drop_append_of_le_length hle
  refine ⟨?_, ?_⟩
  · rw [hs, hr.1, hdiv, Proof.MdStream.Md.compressList_add, Proof.MdStream.Md.compressList_append _ hle, hdrop]
  · rw [hmod, hb, hdiv, Nat.mul_add, ← List.drop_drop, hdrop]

/-- The bytes written, read back. -/
theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem (by simp [bytesAt])
  intro j h₁ h₂
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp [h₂, List.getD_eq_getElem?_getD]

/-! ## `update` -/

/-- What `update` absorbs: the bytes buffered for a message of `cnt` bytes,
then the `len` at `d`. -/
def updBytes (m : Mem) (st : Addr) (cnt : BitVec 64) (d : Addr) (len : Nat) : List Byte :=
  bytesAt m (st + BitVec.ofNat 64 20) (cnt.toNat % 64) ++ bytesAt m d len

/-- The state at `rdi` after `update` of the `rcx` bytes at `rdx`, after
`rsi`. -/
def updMem (a : Arch) : Mem :=
  let x := updBytes a.mem (a.gpr .rdi) (a.gpr .rsi) (a.gpr .rdx) (a.gpr .rcx).toNat
  writeBytes (writeState a.mem (a.gpr .rdi) (md.compressList (md.stateAt a.mem (a.gpr .rdi)) x (x.length / 64)))
    (a.gpr .rdi + BitVec.ofNat 64 20) (x.drop (64 * (x.length / 64)))

def sha1Update : IcallFn := memFn updMem

/-- What `update` does, from an entry its contract holds of. -/
theorem update_run : ∀ s₁ : State, (Spec.HashFns.updateContract T abi 8).pre s₁ → Frame s₁.wr s₁.mem (updMem s₁.arch) ∧
    (∀ r ∈ s₁.wr, r.Disjoint ⟨s₁.gpr .rsp, 8⟩) ∧
      (Spec.HashFns.updateContract T abi 8).post s₁ (s₁.withArch { s₁.arch with mem := updMem s₁.arch }) := by
  intro s₁ hp
  sig_pre [Spec.HashFns.updateContract, Spec.HashFns.updateSig, abi, argRegs, stackBelow] at hp
  obtain ⟨-, -, hwr, -, -, -, dR, -, dRs, -, -, -, bs, -, -⟩ := hp
  have hxl : ∀ x : List Byte, (x.drop (64 * (x.length / 64))).length < 64 := fun x => by
    simp only [List.length_drop]; have := Nat.div_add_mod x.length 64; have := Nat.mod_lt x.length (by decide : 0 < 64)
    omega
  refine ⟨?_, fun r hr => ?_, ?_⟩
  · rw [hwr]
    refine Frame.mono ((frame_writeState _ _ _ (n := 84) (by decide)).trans
      (writeBytes_frame _ _ _ (Offset.contains_base _ (d := 20) (k := 84)
        (Nat.add_le_add_left (Nat.le_of_lt (hxl _)) 20) (by decide)))) fun r hr => ?_
    rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..
  · rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dR.symm
    · exact dRs.symm
  · unfold Spec.HashFns.updateContract
    sig_reduce [Spec.HashFns.updateSig, Spec.HashFns.updatePost, abi, argRegs]
    intro msg hr hc
    rw [BitVec.setWidth_eq] at hc ⊢
    have hr' := Proof.Sha1.repr_iff.mp hr
    refine Proof.Sha1.repr_iff.mpr ?_
    have hbuf : bytesAt s₁.mem (s₁.gpr .rdi + BitVec.ofNat 64 20) ((s₁.gpr .rsi).toNat % 64) =
        msg.drop (64 * (msg.length / 64)) := by
      rw [hc, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 2 ^ 64)]; exact hr'.2
    obtain ⟨x, hxe⟩ : ∃ x, x = msg.drop (64 * (msg.length / 64)) ++
        bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat := ⟨_, rfl⟩
    have hx := hxl x
    have hm : updMem s₁.arch = writeBytes (writeState s₁.mem (s₁.gpr .rdi)
        (md.compressList (md.stateAt s₁.mem (s₁.gpr .rdi)) x (x.length / 64)))
        (s₁.gpr .rdi + BitVec.ofNat 64 20) (x.drop (64 * (x.length / 64))) := by
      simp only [updMem, updBytes, State.arch]; rw [hbuf, hxe]
    rw [hm]
    refine repr_append md (by decide) hr' ?_ ?_ <;> rw [← hxe]
    · rw [md.stateAt_congr fun i hi => writeBytes_before _ _ _ hi (by omega)]
      exact stateAt_writeState _ _ _
    · have e : x.length % 64 = (x.drop (64 * (x.length / 64))).length := by
        simp only [List.length_drop]; have := Nat.div_add_mod x.length 64; omega
      rw [e]
      exact bytesAt_writeBytes_self _ _ _ (by omega)

theorem update_meets {stack : Nat} {s : State} {a : Addr} (h : s.funs a = some sha1Update) :
    FnMeets abi (fun A n => Spec.HashFns.updateContract T A n) 8 stack s a :=
  meets_of h update_run

/-! ## `finalize` -/

/-- The digest of the message of `cnt` bytes whose state is at `st`: its
buffered bytes padded, compressed into its hash value. -/
def finDigest (m : Mem) (st : Addr) (cnt : BitVec 64) : List Byte :=
  md.digest (md.compressList (md.stateAt m st)
    (bytesAt m (st + BitVec.ofNat 64 20) (cnt.toNat % 64) ++ [0x80] ++
      List.replicate ((2 * 64 - 8 - 1 - cnt.toNat % 64) % 64) 0 ++ md.lenOf cnt)
    ((cnt.toNat % 64 + 1 + (2 * 64 - 8 - 1 - cnt.toNat % 64) % 64 + 8) / 64))

/-- The digest of the message the state at `rdi` represents, after `rsi`
bytes, to `rdx`. -/
def finMem (a : Arch) : Mem := writeBytes a.mem (a.gpr .rdx) (finDigest a.mem (a.gpr .rdi) (a.gpr .rsi))

def sha1Finalize : IcallFn := memFn finMem

/-- What `finalize` does, from an entry its contract holds of. -/
theorem finalize_run : ∀ s₁ : State, (Spec.HashFns.finalizeContract T abi 8).pre s₁ → Frame s₁.wr s₁.mem (finMem s₁.arch) ∧
    (∀ r ∈ s₁.wr, r.Disjoint ⟨s₁.gpr .rsp, 8⟩) ∧
      (Spec.HashFns.finalizeContract T abi 8).post s₁ (s₁.withArch { s₁.arch with mem := finMem s₁.arch }) := by
  intro s₁ hp
  sig_pre [Spec.HashFns.finalizeContract, Spec.HashFns.finalizeSig, abi, argRegs, stackBelow] at hp
  obtain ⟨-, -, hwr, -, -, -, dR, dRo, dRs, -, -, -, -, -, -⟩ := hp
  have hdl : ∀ m st c, (finDigest m st c).length = 20 := fun _ _ _ => md.digest_length _
  refine ⟨?_, fun r hr => ?_, ?_⟩
  · rw [hwr]
    refine Frame.mono (writeBytes_frame _ _ _ (by rw [hdl]; exact Region.contains_self _ _)) fun r hr => ?_
    rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dR.symm
    · exact dRo.symm
    · exact dRs.symm
  · unfold Spec.HashFns.finalizeContract
    sig_reduce [Spec.HashFns.finalizeSig, Spec.HashFns.finalizePost, abi, argRegs]
    intro msg hr hl hc
    rw [BitVec.setWidth_eq] at hc
    have hr' := Proof.Sha1.repr_iff.mp hr
    have e := bytesAt_writeBytes_self s₁.mem (s₁.gpr .rdx) (finDigest s₁.mem (s₁.gpr .rdi) (s₁.gpr .rsi))
      (by rw [hdl]; decide)
    rw [hdl] at e
    show List.take 20 (bytesAt (writeBytes s₁.mem (s₁.gpr .rdx) (finDigest s₁.mem (s₁.gpr .rdi) (s₁.gpr .rsi)))
      (s₁.gpr .rdx) 20) = _
    rw [e, List.take_of_length_le (by rw [hdl]), Proof.Sha1.hash_eq,
      md.hash_eq Spec.Sha1.H0 msg ((msg.length % 64 + 1 + (2 * 64 - 8 - 1 - msg.length % 64) % 64 + 8) / 64)
        (by decide) (by omega)]
    simp only [finDigest]
    rw [hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl, md.lenOf_eq _ trivial, hr'.2, ← hr'.1]

theorem finalize_meets {stack : Nat} {s : State} {a : Addr} (h : s.funs a = some sha1Finalize) :
    FnMeets abi (fun A n => Spec.HashFns.finalizeContract T A n) 8 stack s a :=
  meets_of h finalize_run

/-! ## Tables -/

/-- A table of SHA-1's streaming functions, in a state whose functions at
its words are these. -/
theorem tableOf_one {stack : Nat} {s : State} {p a₀ a₁ a₂ : Addr}
    (h₀ : s.funs a₀ = some sha1Init) (h₁ : s.funs a₁ = some sha1Update) (h₂ : s.funs a₂ = some sha1Finalize)
    (r₀ : s.mem.readW p 64 = a₀) (r₁ : s.mem.readW (p + 8) 64 = a₁) (r₂ : s.mem.readW (p + 16) 64 = a₂) :
    Spec.HashFns.tableOf 1 s.mem p (fun a K n => FnMeets abi K n stack s a) := by
  simp only [Spec.HashFns.tableOf, streaming_one, Spec.HashFns.table, r₀, r₁, r₂]
  exact ⟨init_meets h₀, update_meets h₁, finalize_meets h₂⟩

/-- The functions of the witnesses' states: SHA-1's streaming functions at
`0x7000`, `0x7100` and `0x7200`. -/
def funs (a : Addr) : Option IcallFn :=
  if a = 0x7000 then some sha1Init else if a = 0x7100 then some sha1Update
  else if a = 0x7200 then some sha1Finalize else none

end VG.Proof.HashFns.X86_64.Witness
