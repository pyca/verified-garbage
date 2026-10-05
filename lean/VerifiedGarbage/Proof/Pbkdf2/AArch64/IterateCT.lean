import VerifiedGarbage.Proof.MdStream.AArch64.Words
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Impl.Pbkdf2.AArch64
import VerifiedGarbage.Proof.Pbkdf2.MdKeys
import VerifiedGarbage.Proof.Pbkdf2.MdKeys
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Hmac.Generic.Implies

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.AArch64.Compress`. -/
section

/-!
# A Merkle–Damgård compression function on AArch64, called on one block

The contract of a compression function with blocks of any size `B` (`compK`,
which is that of the streaming proofs, `Proof/MdStream/AArch64/Common.lean`,
for any block size), what its callers need of an implementation (`CompOk`:
correct, constant time, without frames), and the call of it on one block
through the streaming code's `compressAt`, in one run (`compressAt_ok`) and in
two (`compressAt_rel`).
-/

namespace VG.Proof.Pbkdf2.AArch64

open VG VG.AArch64 VG.Proof.MdStream
open VG.Impl.MdStream.AArch64 (compressAt compressWith mov)
open VG.Proof.MdStream.AArch64 (Upd wp_mov wp_movz)

section
variable {B N L : Nat} (H : Md B N L) (so : Nat)

/-- The contract of the compression function: updates the `N`-byte hash
value at `x0` with the `x2` blocks of `B` bytes at `x1`, with scratch space
`x3` (`so` bytes). -/
def compK : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, N⟩
    let blocks : Region := ⟨s.gpr .x1, B * (s.gpr .x2).toNat⟩
    let scratch : Region := ⟨s.gpr .x3, so⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' :=
    H.stateAt s'.mem (s.gpr .x0) =
      H.compressBlocks (H.stateAt s.mem (s.gpr .x0)) s.mem (s.gpr .x1) (s.gpr .x2).toNat
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- What a caller needs of an implementation of the compression function:
that it is correct and constant time, pushes no frames, and its checked
instructions do not write callee-saved SIMD registers. -/
structure CompOk (code : Prog isa) : Prop where
  verified : ∀ s, (VG.Proof.Pbkdf2.AArch64.compK H so).pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (VG.Proof.Pbkdf2.AArch64.compK H so).post s s'
  ct : ConstantTime isa (VG.Proof.Pbkdf2.AArch64.compK H so).pre (VG.Proof.Pbkdf2.AArch64.compK H so).pub code
  noFrames : code.noFrames = true
  /-- Existing MD wrappers require untouched callee-saved SIMD registers. -/
  keepsV : code.allInstrs keepsV = true

end

section
variable {B N L : Nat} {H : Md B N L} {so : Nat}

/-- What the call of the compression function on the block at `x1`, into the
hash value at `x19`, with scratch space at `x20`, needs. -/
structure CallOk (s : State) (N B so : Nat) (st scr src : Addr) : Prop where
  x19 : s.gpr .x19 = st
  x20 : s.gpr .x20 = scr
  x1 : s.gpr .x1 = src
  st_scr : Region.Disjoint ⟨st, N⟩ ⟨scr, so⟩
  src_st : Region.Disjoint ⟨src, B⟩ ⟨st, N⟩
  src_scr : Region.Disjoint ⟨src, B⟩ ⟨scr, so⟩
  cov : Covers [⟨src, B⟩, ⟨st, N⟩, ⟨scr, so⟩] (s.rd ++ s.wr)
  covW : Covers [⟨st, N⟩, ⟨scr, so⟩] s.wr

theorem one_toNat : (BitVec.setWidth 64 (1 : BitVec 16)).toNat = 1 := rfl

/-- The state after the instructions that set up the call. -/
structure CSetup (s t : State) : Prop where
  x0 : t.gpr .x0 = s.gpr .x19
  x1 : t.gpr .x1 = s.gpr .x1
  x2 : t.gpr .x2 = BitVec.setWidth 64 (1 : BitVec 16)
  x3 : t.gpr .x3 = s.gpr .x20
  keep : ∀ r ∈ preserved, t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem csetup_ok (s : State) :
    WP isa (.block [mov .x0 .x19, .movz .x .x2 1 0, mov .x3 .x20]) s (VG.Proof.Pbkdf2.AArch64.CSetup s) := by
  refine wp_mov fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_mov fun s₃ u₃ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_, by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.rd, u₂.rd, u₁.rd],
    by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.sp, u₂.sp, u₁.sp]⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₃.other _ (by decide), u₂.gpr]
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  · have : r ≠ .x0 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₃.other _ this.2.2, u₂.other _ this.2.1, u₁.other _ this.1]

theorem call_pre {s t : State} {st scr src : Addr} (h : VG.Proof.Pbkdf2.AArch64.CallOk s N B so st scr src) (hs : VG.Proof.Pbkdf2.AArch64.CSetup s t) :
    (VG.Proof.Pbkdf2.AArch64.compK H so).pre (t.callEntry.withRegions [⟨src, B * (t.callEntry.gpr .x2).toNat⟩] [⟨st, N⟩, ⟨scr, so⟩]) := by
  have c0 : t.callEntry.gpr .x0 = st := (State.callEntry_gpr _ (by decide)).trans (hs.x0.trans h.x19)
  have c1 : t.callEntry.gpr .x1 = src := (State.callEntry_gpr _ (by decide)).trans (hs.x1.trans h.x1)
  have c2 : t.callEntry.gpr .x2 = BitVec.setWidth 64 (1 : BitVec 16) :=
    (State.callEntry_gpr _ (by decide)).trans hs.x2
  have c3 : t.callEntry.gpr .x3 = scr := (State.callEntry_gpr _ (by decide)).trans (hs.x3.trans h.x20)
  simp only [VG.Proof.Pbkdf2.AArch64.compK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, c0, c1, c2, c3, VG.Proof.Pbkdf2.AArch64.one_toNat,
    Nat.mul_one]
  exact ⟨trivial, trivial, h.st_scr, h.src_st, h.src_scr⟩

theorem c2_eq (t : State) (hs : t.gpr .x2 = BitVec.setWidth 64 (1 : BitVec 16)) :
    B * (t.callEntry.gpr .x2).toNat = B := by
  rw [State.callEntry_gpr _ (by decide), hs, VG.Proof.Pbkdf2.AArch64.one_toNat, Nat.mul_one]

/-- Compressing the block at `x1` into the hash value at `x19`, with scratch
space at `x20`: the callee-saved registers other than `x30` are kept. -/
theorem compressAt_ok {name : String} {code : Prog isa} (hf : VG.Proof.Pbkdf2.AArch64.CompOk H so code) {s : State}
    {st scr src : Addr} (h : VG.Proof.Pbkdf2.AArch64.CallOk s N B so st scr src) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      s'.sp = s.sp → Frame [⟨st, N⟩, ⟨scr, so⟩] s.mem s'.mem →
      H.stateAt s'.mem st = H.compress (H.stateAt s.mem st) (H.blockAt s.mem src) → Q s') :
    WP isa (compressAt name code) s Q := by
  unfold compressAt compressWith
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.AArch64.csetup_ok s) fun t hs => ?_)
  have e := VG.Proof.Pbkdf2.AArch64.c2_eq (B := B) t hs.x2
  have hpre := VG.Proof.Pbkdf2.AArch64.call_pre (H := H) h hs
  rw [e] at hpre
  refine WP.call (k := VG.Proof.Pbkdf2.AArch64.compK H so) hf.verified hpre ?_ ?_ ?_ hf.noFrames
  · rw [hs.rd, hs.wr]; simpa using h.cov
  · rw [hs.wr]; exact h.covW
  · intro s' hrd hwr hsp hfr hcs _ hpost
    have c0 : t.callEntry.gpr .x0 = st := (State.callEntry_gpr _ (by decide)).trans (hs.x0.trans h.x19)
    have c1 : t.callEntry.gpr .x1 = src := (State.callEntry_gpr _ (by decide)).trans (hs.x1.trans h.x1)
    have c2 : (t.callEntry.gpr .x2).toNat = 1 := by
      rw [State.callEntry_gpr _ (by decide), hs.x2, VG.Proof.Pbkdf2.AArch64.one_toNat]
    simp only [VG.Proof.Pbkdf2.AArch64.compK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2,
      hs.mem] at hpost
    rw [hs.mem] at hfr
    refine hQ s' (hrd.trans hs.rd) (hwr.trans hs.wr) (fun r hr h30 => (hcs r hr h30).trans (hs.keep r hr))
      (hsp.trans hs.sp) hfr ?_
    rw [hpost, Md.compressBlocks_one]

/-- `compressAt` is constant time, in runs that call it on the same regions. -/
theorem compressAt_rel {name : String} {code : Prog isa} (hf : VG.Proof.Pbkdf2.AArch64.CompOk H so code) {st scr src : Addr}
    {P' : State → State → Prop}
    (hP : ∀ s₁ s₂, P' s₁ s₂ → VG.Proof.Pbkdf2.AArch64.CallOk s₁ N B so st scr src ∧ VG.Proof.Pbkdf2.AArch64.CallOk s₂ N B so st scr src ∧ s₁.sp = s₂.sp) :
    RelCT isa P' (compressAt name code) fun _ _ => True := by
  unfold compressAt compressWith
  have su := (RelCT.taint (A := taint) (P := P') (Taint.ofRegs [])
    (fun s₁ s₂ hp => ⟨(hP s₁ s₂ hp).2.2, fun r hr => by simp at hr⟩)
    (c := .block [mov .x0 .x19, .movz .x .x2 1 0, mov .x3 .x20]) (by taint_decide)).wpDep
      (F := VG.Proof.Pbkdf2.AArch64.CSetup) fun s₁ s₂ _ => ⟨VG.Proof.Pbkdf2.AArch64.csetup_ok s₁, VG.Proof.Pbkdf2.AArch64.csetup_ok s₂⟩
  refine su.seq (RelCT.call (k := VG.Proof.Pbkdf2.AArch64.compK H so) hf.verified hf.ct [⟨src, B⟩] [⟨st, N⟩, ⟨scr, so⟩]
    fun t₁ t₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => ?_)
  obtain ⟨c₁, c₂, hsp⟩ := hP σ₁ σ₂ hp
  have p₁ := VG.Proof.Pbkdf2.AArch64.call_pre (H := H) c₁ h₁
  have p₂ := VG.Proof.Pbkdf2.AArch64.call_pre (H := H) c₂ h₂
  rw [VG.Proof.Pbkdf2.AArch64.c2_eq t₁ h₁.x2] at p₁
  rw [VG.Proof.Pbkdf2.AArch64.c2_eq t₂ h₂.x2] at p₂
  refine ⟨p₁, p₂, ?_, by rw [h₁.rd, h₁.wr]; simpa using c₁.cov, by rw [h₁.wr]; exact c₁.covW,
    by rw [h₂.rd, h₂.wr]; simpa using c₂.cov, by rw [h₂.wr]; exact c₂.covW⟩
  simp only [VG.Proof.Pbkdf2.AArch64.compK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    h₁.x0, h₂.x0, h₁.x1, h₂.x1, h₁.x2, h₂.x2, h₁.x3, h₂.x3, c₁.x19, c₂.x19, c₁.x1, c₂.x1, c₁.x20, c₂.x20,
    h₁.sp, h₂.sp, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

end

end VG.Proof.Pbkdf2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.AArch64.Copy`. -/
section

/-!
# PBKDF2-HMAC's iteration on AArch64: copying words

What `n` copies of a 32-bit word (`cp32`, `Impl/Pbkdf2/AArch64.lean`) write.
-/

namespace VG.Proof.Pbkdf2.AArch64

open VG VG.AArch64
open VG.Impl.Pbkdf2.AArch64 (cp32)
open VG.Proof.MdStream.AArch64 (wp_ldr32 wp_str32 add_ofNat)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil)
open VG.Proof.Hmac.Common (copy_mem bytesAt_zero)
open VG.Spec.Sha256 (bytesAt)

/-- `n` copies of 32-bit words write the `4 n` bytes at `src + o₁` to `dst + o₂`. -/
theorem copy32_ok {src dst : Reg} (hs : src ≠ .x9) (hd : dst ≠ .x9) (o₁ o₂ : Nat) (n : Nat)
    (h₁ : o₁ % 4 = 0 ∧ o₁ + 4 * n ≤ 4096 * 4) (h₂ : o₂ % 4 = 0 ∧ o₂ + 4 * n ≤ 4096 * 4) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * k)) 4) →
    Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) (4 * n) (s.gpr dst + BitVec.ofNat 64 o₂) (4 * n) →
    (∀ s', (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = VG.WriteBytes.writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (4 * n)) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (cp32 src dst o₁ o₂) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl rfl (by rw [Nat.mul_zero, bytesAt_zero, VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro rest s Q hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih ⟨h₁.1, by omega⟩ ⟨h₂.1, by omega⟩ _ s Q (fun j hj => hin j (by omega))
      (fun j hj => hout j (by omega)) (fun x hx hy => hsep x (by omega) (by omega))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [cp32, List.cons_append, List.nil_append]
    refine wp_ldr32 (a := s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * n)) ⟨by omega, by omega⟩
      (by rw [g₁ _ hs, VG.Proof.MdStream.AArch64.add_ofNat]) (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_str32 (a := s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * n)) ⟨by omega, by omega⟩
      (by rw [u₂.other _ hd, g₁ _ hd, VG.Proof.MdStream.AArch64.add_ofNat]) (by rw [u₂.wr, wr₁]; exact hout n (by omega))
      fun s₃ g₃ => k s₃ (fun r hr => by rw [g₃.gpr, u₂.other r hr, g₁ r hr])
        (by rw [g₃.rd, u₂.rd, rd₁]) (by rw [g₃.wr, u₂.wr, wr₁]) (by rw [g₃.sp, u₂.sp, sp₁]) ?_
    have hlt : 4 * n + 4 < 2 ^ 64 := by omega
    rw [g₃.mem, u₂.gpr, u₂.mem, m₁, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq,
      Nat.mul_succ]
    exact copy_mem s.mem _ _ n 4 (by rwa [← Nat.mul_succ]) hlt

end VG.Proof.Pbkdf2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.AArch64.Iterate`. -/
section

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on AArch64

The same proof as on x86-64 (`Proof/Pbkdf2/X86_64/Iterate.lean`): the
iteration (`Impl/Pbkdf2/AArch64.lean`) is correct for any hash function the
generic streaming proofs describe (`Md`), whose code stores the length field
and writes the digest as `Shape` says, with any correct compression function
(`CompOk`), used as a black box through its proof; `Md.hmac_step` says that
its two compressions per step compute HMAC.

The first instruction zero-extends `n`; the rest (`main`) runs from that
state, `zext s₀`, and the lemmas describe it in terms of the entry state
`s₀`.
-/

namespace VG.Proof.Pbkdf2.AArch64

open VG VG.AArch64
open VG.Impl.Pbkdf2.AArch64 (Params raO hvO blkO loadKey padFrom xorW compressBlock body prologue epilogue
  main iterate)
open VG.Impl.MdStream.AArch64 (mov save restore saved)
open VG.Proof.MdStream (Md)
open VG.Proof.MdStream.AArch64 (Dims Upd Mupd wp_mov wp_movz wp_addImm wp_subImm wp_str wp_str32 wp_ldr
  wp_ldr32 Saved saveMem saveMem_saved saveMem_frame saved_offset save_ok restore_ok preserved_of untouched
  ofNat_pred ofNat_beq_zero add_ofNat setWidth32 eval_zero eval_nonzero)
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame writeBytes_append)
open VG.Proof.Hmac.Common (bytesAt_add bytesAt_length bytesAt_writeBytes_sep bytesAt_writeBytes_self
  writeBytes_at bytesAt_getD')
open VG.Proof.Hmac.Generic.Common (bytesAt_take bytesAt_writeBytes_self')
open VG.Spec.Hmac (StreamingHash xorPad ipad opad hmacBlockKey)

/-! ## The contract -/

/-- The contract the proof is written against: `VG.Spec.Pbkdf2.iterateContract`
of the streaming hash function `S` with `W` words of scratch space, on
AArch64. The function uses no stack. -/
def iterK (S : StreamingHash) (W : Nat) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 2 * S.stateBytes⟩
    let u : Region := ⟨s.gpr .x1, S.digestBytes⟩
    let t : Region := ⟨s.gpr .x3, S.digestBytes⟩
    let scratch : Region := ⟨s.gpr .x4, 8 * W⟩
    s.rd = [key, u] ∧ s.wr = [t, scratch] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch ∧
    (s.gpr .x0).toNat + 2 * S.stateBytes ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8 * W ≤ 2 ^ 64
  post s s' := ∀ k0, k0.length = S.H.blockSize →
    S.Repr s.mem (s.gpr .x0) (xorPad k0 ipad) →
    S.Repr s.mem (s.gpr .x0 + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .x3) S.digestBytes =
      Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) ((s.gpr .x2).setWidth 32).toNat
        (bytesAt s.mem (s.gpr .x1) S.digestBytes) (bytesAt s.mem (s.gpr .x3) S.digestBytes)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    (s₁.gpr .x2).setWidth 32 = (s₂.gpr .x2).setWidth 32 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- What `P.len` and `P.out` must do: `P.len` stores the length field for the
byte count in `x22` at `x19 + N + B - L`, writing only `x9` and `x12`, and
`P.out` writes the digest of the hash value at `x19` to `x21`, writing only
`x9`. -/
structure Shape {P : Params} (H : Md P.B P.N P.L) : Prop where
  lenKeepsV : P.len.all keepsV = true
  outKeepsV : P.out.all keepsV = true
  len : ∀ s : State, InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 (P.N + P.B - P.L)) P.L →
    WP isa (.block P.len) s fun s' => (∀ r, r ≠ .x9 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (s.gpr .x19 + BitVec.ofNat 64 (P.N + P.B - P.L)) (H.lenOf (s.gpr .x22))
  out : ∀ s : State, InRegions (s.rd ++ s.wr) (s.gpr .x19) P.N → InRegions s.wr (s.gpr .x21) P.N →
    Region.Disjoint ⟨s.gpr .x19, P.N⟩ ⟨s.gpr .x21, P.N⟩ →
    WP isa (.block P.out) s fun s' => (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (s.gpr .x21) (H.digest (H.stateAt s.mem (s.gpr .x19)))

/-- The streaming proofs' `Shape`. -/
theorem Shape.ofMd {P : VG.Impl.MdStream.AArch64.Params} {H : Md P.B P.N P.L} (h : MdStream.AArch64.Shape H) :
    VG.Proof.Pbkdf2.AArch64.Shape (P := Impl.Pbkdf2.AArch64.ofMd P) H :=
  ⟨h.lenKeepsV, h.outKeepsV, h.len, h.out⟩

/-- The sizes the proof supports, checked for each hash function by `decide`:
words of 4 bytes, a digest of at most the hash value, room for the padding
in the block after the digest and after the hash value, and room in the
scratch space for the compression function's, our caller's registers, our
return address, the hash value and the block. -/
structure Sizes (P : Params) (D W : Nat) : Prop where
  dims : Dims P.md
  B : P.B = 64 ∨ P.B = 128
  N4 : P.N % 4 = 0
  D4 : D % 4 = 0
  L4 : P.L % 4 = 0
  D0 : 0 < D
  DN : D ≤ P.N
  NL : P.N + P.L ≤ P.B
  pad : D + 4 ≤ P.B - P.L
  fits : P.so + 56 + P.N + P.B ≤ 8 * W
  W : W ≤ 1024

/-! ## The precondition -/

section
variable (P : Params) (D W : Nat) (s₀ : State)

abbrev key : Addr := s₀.gpr .x0
abbrev up : Addr := s₀.gpr .x1
abbrev tp : Addr := s₀.gpr .x3
abbrev scr : Addr := s₀.gpr .x4
/-- The number of steps. -/
abbrev nn : Nat := ((s₀.gpr .x2).setWidth 32).toNat
abbrev keyR : Region := ⟨VG.Proof.Pbkdf2.AArch64.key s₀, 2 * (P.N + P.B)⟩
abbrev uR : Region := ⟨VG.Proof.Pbkdf2.AArch64.up s₀, D⟩
abbrev tR : Region := ⟨VG.Proof.Pbkdf2.AArch64.tp s₀, D⟩
abbrev scR : Region := ⟨VG.Proof.Pbkdf2.AArch64.scr s₀, 8 * W⟩
/-- The hash value being compressed, and the block. -/
abbrev hv : Addr := VG.Proof.Pbkdf2.AArch64.scr s₀ + BitVec.ofNat 64 (P.so + 56)
abbrev blk : Addr := VG.Proof.Pbkdf2.AArch64.scr s₀ + BitVec.ofNat 64 (P.so + 56 + P.N)

end

structure Pre (P : Params) (D W : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Pbkdf2.AArch64.keyR P s₀, VG.Proof.Pbkdf2.AArch64.uR D s₀]
  wr : s₀.wr = [VG.Proof.Pbkdf2.AArch64.tR D s₀, VG.Proof.Pbkdf2.AArch64.scR W s₀]
  k_t : (VG.Proof.Pbkdf2.AArch64.keyR P s₀).Disjoint (VG.Proof.Pbkdf2.AArch64.tR D s₀)
  k_s : (VG.Proof.Pbkdf2.AArch64.keyR P s₀).Disjoint (VG.Proof.Pbkdf2.AArch64.scR W s₀)
  u_t : (VG.Proof.Pbkdf2.AArch64.uR D s₀).Disjoint (VG.Proof.Pbkdf2.AArch64.tR D s₀)
  u_s : (VG.Proof.Pbkdf2.AArch64.uR D s₀).Disjoint (VG.Proof.Pbkdf2.AArch64.scR W s₀)
  t_s : (VG.Proof.Pbkdf2.AArch64.tR D s₀).Disjoint (VG.Proof.Pbkdf2.AArch64.scR W s₀)

theorem pre_of {P : Params} {D W : Nat} {S : StreamingHash} (hS : S.stateBytes = P.N + P.B)
    (hD : S.digestBytes = D) {s₀ : State} (h : (VG.Proof.Pbkdf2.AArch64.iterK S W).pre s₀) : VG.Proof.Pbkdf2.AArch64.Pre P D W s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, -, -⟩ := h
  simp only [hS, hD] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

/-! ## The parts of the scratch space -/

section
variable {P : Params} {D W : Nat} (hz : VG.Proof.Pbkdf2.AArch64.Sizes P D W)
include hz

theorem so_le : P.so ≤ 1024 := hz.dims.so.2
theorem so8 : P.so % 8 = 0 ∧ P.so ≤ 1024 := hz.dims.so
theorem saved_off {q : Reg × Nat} (hq : q ∈ saved P.md) : P.so ≤ q.2 ∧ q.2 + 8 ≤ P.so + 48 :=
  saved_offset hz.dims hq
theorem N_le : P.N ≤ 64 := hz.dims.N.2
theorem B_le : P.B ≤ 128 := by rcases hz.B with h | h <;> omega
theorem B_ge : 64 ≤ P.B := by rcases hz.B with h | h <;> omega

omit hz in
theorem scr_sub (s₀ : State) {a n : Nat} (h : a + n ≤ 8 * W) :
    Region.Sub ⟨VG.Proof.Pbkdf2.AArch64.scr s₀ + BitVec.ofNat 64 a, n⟩ (VG.Proof.Pbkdf2.AArch64.scR W s₀) :=
  Offset.sub_base _ h

end

theorem md_so (P : Params) : P.md.so = P.so := rfl

theorem add0 (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-! ## The registers during a step -/

/-- The registers `main` keeps between its pieces: ours but the count, and
the callee-saved ones it never writes. -/
abbrev kept : List Reg := [.x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27, .x28]

theorem ne9 : ∀ r ∈ VG.Proof.Pbkdf2.AArch64.kept, r ≠ .x9 := by decide
theorem ne10 : ∀ r ∈ VG.Proof.Pbkdf2.AArch64.kept, r ≠ .x10 := by decide
theorem ne12 : ∀ r ∈ VG.Proof.Pbkdf2.AArch64.kept, r ≠ .x12 := by decide
theorem ne1 : ∀ r ∈ VG.Proof.Pbkdf2.AArch64.kept, r ≠ .x1 := by decide
theorem ne24 : ∀ r ∈ VG.Proof.Pbkdf2.AArch64.kept, r ≠ .x24 := by decide
theorem kept_preserved : ∀ r ∈ VG.Proof.Pbkdf2.AArch64.kept, r ∈ preserved ∧ r ≠ .x30 := by decide
theorem untouched_kept : ∀ r ∈ untouched, r ∈ VG.Proof.Pbkdf2.AArch64.kept := by decide
theorem untouched_ne22 : ∀ r ∈ untouched, r ≠ .x22 := by decide
theorem untouched_ne30 : ∀ r ∈ untouched, r ≠ .x30 := by decide
theorem untouched_not_saved (P : VG.Impl.MdStream.AArch64.Params) : ∀ r ∈ untouched, r ∉ (saved P).map Prod.fst := by
  simp only [saved, List.map_cons, List.map_nil]; decide

/-- What holds between the pieces of a step: the regions, our registers, the
callee-saved registers we never write, the stack pointer, and memory outside
the scratch space and `T` as on entry. -/
structure Regs (P : Params) (D W : Nat) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  x19 : s.gpr .x19 = VG.Proof.Pbkdf2.AArch64.hv P s₀
  x20 : s.gpr .x20 = VG.Proof.Pbkdf2.AArch64.scr s₀
  x21 : s.gpr .x21 = VG.Proof.Pbkdf2.AArch64.blk P s₀
  x22 : s.gpr .x22 = VG.Proof.Pbkdf2.AArch64.key s₀
  x23 : s.gpr .x23 = VG.Proof.Pbkdf2.AArch64.tp s₀
  cs : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  frame : Frame [VG.Proof.Pbkdf2.AArch64.tR D s₀, VG.Proof.Pbkdf2.AArch64.scR W s₀] s₀.mem s.mem

section
variable {P : Params} {D W : Nat} (hz : VG.Proof.Pbkdf2.AArch64.Sizes P D W) {s₀ : State} (hp : VG.Proof.Pbkdf2.AArch64.Pre P D W s₀)

/-- `Regs` after code that keeps our registers and writes only memory in the
regions it allows. -/
theorem Regs.write {s s' : State} (h : VG.Proof.Pbkdf2.AArch64.Regs P D W s₀ s) (hg : ∀ r ∈ VG.Proof.Pbkdf2.AArch64.kept, s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hm : Frame [VG.Proof.Pbkdf2.AArch64.tR D s₀, VG.Proof.Pbkdf2.AArch64.scR W s₀] s.mem s'.mem) : VG.Proof.Pbkdf2.AArch64.Regs P D W s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  x19 := (hg _ (by decide)).trans h.x19
  x20 := (hg _ (by decide)).trans h.x20
  x21 := (hg _ (by decide)).trans h.x21
  x22 := (hg _ (by decide)).trans h.x22
  x23 := (hg _ (by decide)).trans h.x23
  cs := fun r hr => (hg r (VG.Proof.Pbkdf2.AArch64.untouched_kept r hr)).trans (h.cs r hr)
  sp := hsp.trans h.sp
  frame := h.frame.trans hm

omit hp in
/-- A part of the scratch space, as a frame of `Regs`. -/
theorem frame_scr {m m' : Mem} {a n : Nat} (h : a + n ≤ 8 * W)
    (hf : Frame [⟨VG.Proof.Pbkdf2.AArch64.scr s₀ + BitVec.ofNat 64 a, n⟩] m m') : Frame [VG.Proof.Pbkdf2.AArch64.tR D s₀, VG.Proof.Pbkdf2.AArch64.scR W s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.Pbkdf2.AArch64.scR W s₀, by simp, VG.Proof.Pbkdf2.AArch64.scr_sub s₀ h⟩

include hz hp

theorem in_scr {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ 8 * W) :
    InRegions s.wr (VG.Proof.Pbkdf2.AArch64.scr s₀ + BitVec.ofNat 64 a) n :=
  ⟨VG.Proof.Pbkdf2.AArch64.scR W s₀, by simp [hwr, hp.wr], Offset.contains_base _ h (by have hz_W := hz.W; omega)⟩

theorem in_blk {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ P.B) :
    InRegions s.wr (VG.Proof.Pbkdf2.AArch64.blk P s₀ + BitVec.ofNat 64 a) n := by
  have hz_fits := hz.fits
  rw [add_ofNat]; exact VG.Proof.Pbkdf2.AArch64.in_scr hz hp hwr (by omega)

theorem in_scr' {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ 8 * W) :
    InRegions (s.rd ++ s.wr) (VG.Proof.Pbkdf2.AArch64.scr s₀ + BitVec.ofNat 64 a) n := by
  obtain ⟨r, hr, hc⟩ := VG.Proof.Pbkdf2.AArch64.in_scr hz hp hwr h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- The hash value at `key + o` into the scratch space. -/
theorem load_ok {H : Md P.B P.N P.L} (hR : H.Reloc) {s : State} (h : VG.Proof.Pbkdf2.AArch64.Regs P D W s₀ s) {o : Nat}
    (ho : o + P.N ≤ 2 * (P.N + P.B)) (ho4 : o % 4 = 0) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [⟨VG.Proof.Pbkdf2.AArch64.hv P s₀, P.N⟩] s.mem s'.mem →
      H.stateAt s'.mem (VG.Proof.Pbkdf2.AArch64.hv P s₀) = H.stateAt s₀.mem (VG.Proof.Pbkdf2.AArch64.key s₀ + BitVec.ofNat 64 o) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (loadKey P o ++ rest)) s Q := by
  have := VG.Proof.Pbkdf2.AArch64.so_le hz; have := VG.Proof.Pbkdf2.AArch64.N_le hz; have := VG.Proof.Pbkdf2.AArch64.B_le hz; have := hz.dims.N; have hz_N4 := hz.N4; have hz_fits := hz.fits
  have hn : 4 * (P.N / 4) = P.N := by omega
  unfold loadKey
  refine VG.Proof.Pbkdf2.AArch64.copy32_ok (by decide) (by decide) o 0 (P.N / 4) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ rest s Q
    (fun j hj => ?_) (fun j hj => ?_) ?_ fun s' g' rd' wr' sp' m' => ?_
  · rw [h.x22, h.rd, hp.rd, add_ofNat]
    exact ⟨VG.Proof.Pbkdf2.AArch64.keyR P s₀, by simp, Offset.contains_base _ (by omega_using [hj, ho]) (by omega)⟩
  · rw [h.x19, h.wr, hp.wr, add_ofNat, add_ofNat]
    exact ⟨VG.Proof.Pbkdf2.AArch64.scR W s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [h.x22, h.x19, hn, add_ofNat, Nat.add_zero]
    exact hp.k_s.sep (Offset.contains_base _ (by omega) (by omega))
      (Offset.contains_base _ (by omega_using [hz_fits]) (by omega))
  rw [h.x19, h.x22, hn, add_ofNat, Nat.add_zero] at m'
  refine k s' g' rd' wr' sp' (by rw [m']; exact VG.WriteBytes.writeBytes_frame _ _ _ (by
    rw [bytesAt_length]; exact Region.contains_self _ _)) ?_
  refine hR _ _ _ _ fun i hi => ?_
  rw [m', writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
    bytesAt_getD' _ _ hi, add_ofNat]
  exact h.frame.bytes (R := VG.Proof.Pbkdf2.AArch64.keyR P s₀) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.k_t
    · exact hp.k_s) (by show 2 * (P.N + P.B) ≤ 2 ^ 64; omega) (by show o + i < 2 * (P.N + P.B); omega_using [hi, ho])

/-- What the call of the compression function needs, with the block's address in `x1`. -/
theorem callOk_of {s : State} (h : VG.Proof.Pbkdf2.AArch64.Regs P D W s₀ s) (h1 : s.gpr .x1 = VG.Proof.Pbkdf2.AArch64.blk P s₀) :
    VG.Proof.Pbkdf2.AArch64.CallOk s P.N P.B P.so (VG.Proof.Pbkdf2.AArch64.hv P s₀) (VG.Proof.Pbkdf2.AArch64.scr s₀) (VG.Proof.Pbkdf2.AArch64.blk P s₀) := by
  have := VG.Proof.Pbkdf2.AArch64.so_le hz; have := VG.Proof.Pbkdf2.AArch64.N_le hz; have := VG.Proof.Pbkdf2.AArch64.B_le hz; have hz_fits := hz.fits
  have hsc : VG.Proof.Pbkdf2.AArch64.scR W s₀ ∈ s.wr := by simp [h.wr, hp.wr]
  refine ⟨h.x19, h.x20, h1, Offset.disjoint_base _ (by omega) (by omega),
    Offset.disjoint _ (.inr (by omega)) (by omega) (by omega), Offset.disjoint_base _ (by omega) (by omega),
    ?_, ?_⟩
  · refine Covers.of_sub fun r hr => ⟨VG.Proof.Pbkdf2.AArch64.scR W s₀, List.mem_append_right _ hsc, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, rfl, by dsimp only; omega⟩
    · exact ⟨_, rfl, by dsimp only; omega⟩
    · exact ⟨0, by simp, by dsimp only; omega⟩
  · refine Covers.of_sub fun r hr => ⟨VG.Proof.Pbkdf2.AArch64.scR W s₀, hsc, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, rfl, by dsimp only; omega⟩
    · exact ⟨0, by simp, by dsimp only; omega⟩

/-- A call of the compression function on the block. -/
theorem cmp_ok {H : Md P.B P.N P.L} {name : String} {code : Prog isa} (hf : VG.Proof.Pbkdf2.AArch64.CompOk H P.so code) {s : State}
    (h : VG.Proof.Pbkdf2.AArch64.Regs P D W s₀ s) {Q : State → Prop}
    (k : ∀ s', VG.Proof.Pbkdf2.AArch64.Regs P D W s₀ s' → s'.gpr .x24 = s.gpr .x24 →
      Frame [⟨VG.Proof.Pbkdf2.AArch64.hv P s₀, P.N⟩, ⟨VG.Proof.Pbkdf2.AArch64.scr s₀, P.so⟩] s.mem s'.mem →
      H.stateAt s'.mem (VG.Proof.Pbkdf2.AArch64.hv P s₀) = H.compress (H.stateAt s.mem (VG.Proof.Pbkdf2.AArch64.hv P s₀)) (H.blockAt s.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀)) →
      Q s') :
    WP isa (compressBlock name code) s Q := by
  have := VG.Proof.Pbkdf2.AArch64.so_le hz; have := VG.Proof.Pbkdf2.AArch64.N_le hz; have := VG.Proof.Pbkdf2.AArch64.B_le hz; have hz_fits := hz.fits
  unfold compressBlock
  refine WP.seq (wp_mov fun s₁ u₁ => WP.block_nil ?_)
  have h₁ := h.write (fun r hr => u₁.other r (VG.Proof.Pbkdf2.AArch64.ne1 r hr)) u₁.rd u₁.wr u₁.sp (by rw [u₁.mem]; exact Frame.refl _ _)
  refine VG.Proof.Pbkdf2.AArch64.compressAt_ok hf (VG.Proof.Pbkdf2.AArch64.callOk_of hz hp h₁ (by rw [u₁.gpr, h.x21])) fun s' hrd hwr hcs hsp hfr hst => ?_
  have cs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r := fun r hr h30 => by
    rw [hcs r hr h30, u₁.other r (by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  rw [u₁.mem] at hfr hst
  refine k s' (h.write (fun r hr => cs r (VG.Proof.Pbkdf2.AArch64.kept_preserved r hr).1 (VG.Proof.Pbkdf2.AArch64.kept_preserved r hr).2)
    (hrd.trans u₁.rd) (hwr.trans u₁.wr) (hsp.trans u₁.sp) (hfr.sub fun r hr => ?_))
    (cs _ (by decide) (by decide)) hfr hst
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨VG.Proof.Pbkdf2.AArch64.scR W s₀, by simp, VG.Proof.Pbkdf2.AArch64.scr_sub s₀ (by omega)⟩
  · exact ⟨VG.Proof.Pbkdf2.AArch64.scR W s₀, by simp, Region.sub_prefix (by omega)⟩

end

/-! ## Words of the block and of `T` -/

theorem wp_eor {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .x d n m :: is)) s Q :=
  MdStream.AArch64.WP.cons (s' := s.write .x d (s.gpr n ^^^ s.gpr m)) (by simp [exec, State.read])
    (k _ (Upd.write64 _ _ _))

theorem xor_setWidth (a b : BitVec 32) : (a.setWidth 64 ^^^ b.setWidth 64).setWidth 32 = a ^^^ b := by
  rw [BitVec.setWidth_xor, setWidth32, setWidth32]

theorem writeW_xor32 (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 32 ^^^ m'.readW b 32) =
      VG.WriteBytes.writeBytes m d (Spec.Pbkdf2.xorBytes (bytesAt m' b 4) (bytesAt m' a 4)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (32 : Nat) / 8 = 4 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    VG.WriteBytes.write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [Spec.Pbkdf2.xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [Spec.Pbkdf2.xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁, Mem.extractLsb'_read _ _ h₁, BitVec.xor_comm]

/-- `T ← T ⊕ U` for the first `n` 32-bit words of `T` at `tp` and `U` at `bp`. -/
theorem xor_ok {tp bp : Addr} {D : Nat} (hd : Region.Disjoint ⟨tp, D⟩ ⟨bp, D⟩) (hD : D ≤ 4096) :
    ∀ n, 4 * n ≤ D → ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .x21 = bp → s.gpr .x23 = tp →
    (∀ k < n, InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (tp + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = VG.WriteBytes.writeBytes s.mem tp
        (Spec.Pbkdf2.xorBytes (bytesAt s.mem tp (4 * n)) (bytesAt s.mem bp (4 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap xorW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ k
    exact k s (fun _ _ _ => rfl) rfl rfl rfl (by simp [bytesAt, Spec.Pbkdf2.xorBytes, VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q hbp h23 hin hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q hbp h23 (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [xorW, List.cons_append, List.nil_append]
    have hw := hout n (by omega)
    refine wp_ldr32 (a := bp + BitVec.ofNat 64 (4 * n)) ⟨by omega, by omega⟩
      (by rw [g₁ _ (by decide) (by decide), hbp]) (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_ldr32 (a := tp + BitVec.ofNat 64 (4 * n)) ⟨by omega, by omega⟩
      (by rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide), h23])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; obtain ⟨r, hr, hc⟩ := hw; exact ⟨r, List.mem_append_right _ hr, hc⟩)
      fun s₃ u₃ => ?_
    refine VG.Proof.Pbkdf2.AArch64.wp_eor fun s₄ u₄ => ?_
    refine wp_str32 (a := tp + BitVec.ofNat 64 (4 * n)) ⟨by omega, by omega⟩
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        g₁ _ (by decide) (by decide), h23])
      (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]; exact hw)
      fun s₅ g₅ => k s₅ (fun r h9 h10 => by
          rw [g₅.gpr, u₄.other r h9, u₃.other r h10, u₂.other r h9, g₁ r h9 h10])
        (by rw [g₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [g₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
        (by rw [g₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    have hl : (Spec.Pbkdf2.xorBytes (bytesAt s.mem tp (4 * n)) (bytesAt s.mem bp (4 * n))).length = 4 * n := by
      rw [Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    rw [g₅.mem, u₄.gpr, u₄.mem, u₃.gpr, u₃.other _ (by decide), u₃.mem, u₂.gpr, u₂.mem, VG.Proof.Pbkdf2.AArch64.xor_setWidth,
      VG.Proof.Pbkdf2.AArch64.writeW_xor32, m₁,
      bytesAt_writeBytes_sep (p := tp + BitVec.ofNat 64 (4 * n)),
      bytesAt_writeBytes_sep (p := bp + BitVec.ofNat 64 (4 * n))]
    · have e := VG.WriteBytes.writeBytes_append s.mem tp _ (Spec.Pbkdf2.xorBytes (bytesAt s.mem (tp + BitVec.ofNat 64 (4 * n)) 4)
        (bytesAt s.mem (bp + BitVec.ofNat 64 (4 * n)) 4))
        (by rw [hl, Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
      rw [hl] at e
      rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, Spec.Pbkdf2.xorBytes, Spec.Pbkdf2.xorBytes,
        Spec.Pbkdf2.xorBytes, List.zipWith_append (by simp [bytesAt])]
    · intro x h₁ h₂
      rw [hl] at h₂
      exact hd x (by simp only [Region.Contains]; omega) (Memory.off_contains h₁ (by omega) (by omega))
    · omega
    · intro x h₁ h₂
      rw [hl] at h₂
      exact Memory.sep_after h₁ h₂ (by omega)
    · omega

/-- Stores of zero (the low 32 bits of `x9`) at `x21 + a + 4 + 4 k`, for `k < n`. -/
theorem zeros_ok {a : Nat} {p : Addr} (ha4 : a % 4 = 0) : ∀ n, a + 4 + 4 * n ≤ 4096 * 4 →
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr .x21 = p → (s.gpr .x9).setWidth 32 = 0 →
    (∀ k < n, InRegions s.wr (p + BitVec.ofNat 64 (a + 4 + 4 * k)) 4) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = VG.WriteBytes.writeBytes s.mem (p + BitVec.ofNat 64 (a + 4)) (List.replicate (4 * n) 0) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).map (fun k => Instr.str .w .x9 .x21 (a + 4 + 4 * k)) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ k
    exact k s rfl rfl rfl rfl (by simp [VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro ha rest s Q hbp hax hout k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih (by omega_using [ha]) _ s Q hbp hax (fun j hj => hout j (by omega)) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_str32 (a := p + BitVec.ofNat 64 (a + 4 + 4 * n)) ⟨by omega, by omega_using [ha]⟩ (by rw [g₁, hbp])
      (by rw [wr₁]; exact hout n (by omega)) fun s₂ g₂ =>
        k s₂ (by rw [g₂.gpr, g₁]) (by rw [g₂.rd, rd₁]) (by rw [g₂.wr, wr₁]) (by rw [g₂.sp, sp₁]) ?_
    rw [g₂.mem, g₁, hax, m₁, Memory.writeW_bytes _ _ (0 : BitVec 32) [0, 0, 0, 0] (by decide),
      Memory.writeBytes_append' _ _ _ (by rw [List.length_replicate, add_ofNat]) (by simp; omega_using [ha]), Nat.mul_succ,
      ← List.replicate_append_replicate]
    rfl

/-- `padFrom a b` writes `0x80` and zeros from byte `a` to byte `b` of the block at `x21`. -/
theorem padFrom_ok {a b : Nat} (hab : a + 4 ≤ b) (h4 : (b - a) % 4 = 0) (ha4 : a % 4 = 0) (hb : b ≤ 4096 * 4)
    {s : State} {p : Addr}
    (hbp : s.gpr .x21 = p) (hout : ∀ k < (b - a) / 4, InRegions s.wr (p + BitVec.ofNat 64 (a + 4 * k)) 4)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = VG.WriteBytes.writeBytes s.mem (p + BitVec.ofNat 64 a) ([0x80] ++ List.replicate (b - a - 1) 0) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (padFrom a b ++ rest)) s Q := by
  unfold padFrom
  simp only [List.cons_append, List.nil_append]
  refine wp_movz fun s₁ u₁ => ?_
  refine wp_str32 (a := p + BitVec.ofNat 64 a) ⟨ha4, by omega_using [hb, hab]⟩ (by rw [u₁.other _ (by decide), hbp])
    (by rw [u₁.wr]; simpa using hout 0 (by omega)) fun s₂ g₂ => ?_
  refine wp_movz fun s₃ u₃ => ?_
  refine VG.Proof.Pbkdf2.AArch64.zeros_ok (a := a) ha4 ((b - a) / 4 - 1) (by omega_using [hb, hab]) rest s₃ Q
    (by rw [u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), hbp]) (by rw [u₃.gpr]; rfl)
    (fun j hj => by
      rw [u₃.wr, g₂.wr, u₁.wr, show a + 4 + 4 * j = a + 4 * (j + 1) by omega]; exact hout (j + 1) (by omega))
    fun s₄ g₄ rd₄ wr₄ sp₄ m₄ => k s₄ (fun r hr => by
      rw [g₄, u₃.other r hr, g₂.gpr, u₁.other r hr]) (by rw [rd₄, u₃.rd, g₂.rd, u₁.rd])
      (by rw [wr₄, u₃.wr, g₂.wr, u₁.wr]) (by rw [sp₄, u₃.sp, g₂.sp, u₁.sp]) ?_
  rw [m₄, u₃.mem, g₂.mem, u₁.gpr, u₁.mem,
    show ((BitVec.setWidth 64 (0x80 : BitVec 16)).setWidth 32 : BitVec 32) = 0x80 from rfl,
    Memory.writeW_bytes _ _ (0x80 : BitVec 32) [0x80, 0, 0, 0] (by decide),
    Memory.writeBytes_append' _ _ _ (by rw [List.length_cons, List.length_cons, List.length_cons,
      List.length_singleton, add_ofNat]) (by simp; omega),
    show b - a - 1 = 3 + 4 * ((b - a) / 4 - 1) by omega, ← List.replicate_append_replicate]
  rfl

/-- `padLen` writes the rest of the block at `p` (`x21`) after its first `D`
bytes, which it keeps: the padding of a `B + D`-byte message, whose length
field `P.len` stores at `x19 + N + B - L`, the block's end. -/
theorem padLen_ok {P : Params} {D : Nat} {H : Md P.B P.N P.L} (hs : VG.Proof.Pbkdf2.AArch64.Shape H) (hok : H.lenOk (P.B + D))
    (hD4 : D % 4 = 0) (hL4 : P.L % 4 = 0) (hB4 : P.B % 4 = 0) (hpad : D + 4 ≤ P.B - P.L) (hB : P.B ≤ 128)
    {s : State} {p : Addr} (hbp : s.gpr .x21 = p)
    (hbx : s.gpr .x19 + BitVec.ofNat 64 (P.N + P.B - P.L) = p + BitVec.ofNat 64 (P.B - P.L))
    (hw : ∀ a n, a + n ≤ P.B → InRegions s.wr (p + BitVec.ofNat 64 a) n) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .x9 → r ≠ .x12 → r ≠ .x22 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → Frame [⟨p, P.B⟩] s.mem s'.mem →
      bytesAt s'.mem (p + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D →
      bytesAt s'.mem p D = bytesAt s.mem p D → WP isa (.block rest) s' Q) :
    WP isa (.block (Impl.Pbkdf2.AArch64.padLen P D ++ rest)) s Q := by
  unfold Impl.Pbkdf2.AArch64.padLen
  simp only [List.append_assoc]
  refine VG.Proof.Pbkdf2.AArch64.padFrom_ok (a := D) (b := P.B - P.L) (by omega) (by omega) (by omega) (by omega_using [hB]) hbp
    (fun j hj => hw _ _ (by omega_using [hj])) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  refine wp_movz fun s₃ u₃ => ?_
  change WP isa (.block (P.len ++ rest)) s₃ Q
  rw [WP.block_append_iff]
  refine WP.mono (hs.len s₃ ?_) fun s₄ ⟨g₄, rd₄, wr₄, sp₄, m₄⟩ => ?_
  · rw [u₃.other _ (by decide), g₂ _ (by decide), hbx, u₃.wr, wr₂]; exact hw _ _ (by omega_using [hpad])
  have zx : (BitVec.ofNat 16 (P.B + D)).setWidth 64 = BitVec.ofNat 64 (P.B + D) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using [hB, hpad]
  rw [u₃.other _ (by decide), g₂ _ (by decide), hbx, u₃.gpr, zx, H.lenOf_eq _ hok, u₃.mem, m₂] at m₄
  have lpz : ([0x80] ++ List.replicate (P.B - P.L - D - 1) 0 : List Byte).length = P.B - P.L - D := by simp; omega_using [hpad]
  have S1 : Mem.Sep p D (p + BitVec.ofNat 64 D) (P.B - P.L - D) := by
    have := Offset.sep p (d := 0) (n := D) (e := D) (k := P.B - P.L - D) (.inl (by omega)) (by omega_using [hB, hpad]) (by omega_using [hB, hpad])
    rwa [VG.Proof.Pbkdf2.AArch64.add0] at this
  have S2 : ∀ {a n : Nat}, a + n ≤ P.B - P.L →
      Mem.Sep (p + BitVec.ofNat 64 a) n (p + BitVec.ofNat 64 (P.B - P.L)) P.L :=
    fun h' => Offset.sep _ (.inl h') (by omega_using [h', hB]) (by omega_using [hB, hpad])
  refine k s₄ (fun r h1 h2 h3 => by rw [g₄ r h1 h2, u₃.other r h3, g₂ r h1]) (by rw [rd₄, u₃.rd, rd₂])
    (by rw [wr₄, u₃.wr, wr₂]) (by rw [sp₄, u₃.sp, sp₂]) ?_ ?_ ?_
  · rw [m₄]
    refine (VG.WriteBytes.writeBytes_frame _ _ _ ?_).trans (VG.WriteBytes.writeBytes_frame _ _ _ ?_)
    · rw [lpz]; exact Offset.contains_base _ (by omega_using [hpad]) (by omega_using [hB, hpad])
    · rw [H.lenBytes_length]; exact Offset.contains_base _ (by omega_using [hpad]) (by omega_using [hB])
  · rw [show P.B - D = (P.B - P.L - D) + P.L by omega_using [hpad], bytesAt_add, add_ofNat p,
      show D + (P.B - P.L - D) = P.B - P.L by omega_using [hpad], m₄,
      bytesAt_writeBytes_self' (H.lenBytes_length _) (by omega_using [hB, hpad]),
      bytesAt_writeBytes_sep _ _ (by rw [H.lenBytes_length]; exact S2 (by omega_using [hpad])) (by omega_using [hB]),
      bytesAt_writeBytes_self' lpz (by omega), Md.tailPad, show P.B - P.L - 1 - D = P.B - P.L - D - 1 by omega_using []]
  · rw [m₄, bytesAt_writeBytes_sep _ _ (by
        rw [H.lenBytes_length]; have := S2 (a := 0) (n := D) (by omega_using [hpad]); rwa [VG.Proof.Pbkdf2.AArch64.add0] at this) (by omega),
      bytesAt_writeBytes_sep _ _ (by rw [lpz]; exact S1) (by omega)]

/-! ## The digest into the block -/

theorem blk_sep (P : Params) (s₀ : State) {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a + n ≤ 2 ^ 32)
    (hb : b + k ≤ 2 ^ 32) (hN : P.so + 56 + P.N ≤ 2 ^ 32) :
    Mem.Sep (VG.Proof.Pbkdf2.AArch64.blk P s₀ + BitVec.ofNat 64 a) n (VG.Proof.Pbkdf2.AArch64.blk P s₀ + BitVec.ofNat 64 b) k := by
  rw [add_ofNat, add_ofNat]
  exact Offset.sep _ (by omega) (by omega) (by omega)

theorem blk0 (P : Params) (s₀ : State) : VG.Proof.Pbkdf2.AArch64.blk P s₀ + BitVec.ofNat 64 0 = VG.Proof.Pbkdf2.AArch64.blk P s₀ := VG.Proof.Pbkdf2.AArch64.add0 _

section
variable {P : Params} {D W : Nat} (hz : VG.Proof.Pbkdf2.AArch64.Sizes P D W) {s₀ : State} (hp : VG.Proof.Pbkdf2.AArch64.Pre P D W s₀)
include hz hp

/-- The digest of the hash value into the block's first `D` bytes, the padding after them as it was. -/
theorem digest_ok {H : Md P.B P.N P.L} (hs : VG.Proof.Pbkdf2.AArch64.Shape H) {s : State} (h : VG.Proof.Pbkdf2.AArch64.Regs P D W s₀ s)
    (hpad : bytesAt s.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [⟨VG.Proof.Pbkdf2.AArch64.blk P s₀, P.N⟩] s.mem s'.mem →
      bytesAt s'.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀) D = (H.digest (H.stateAt s.mem (VG.Proof.Pbkdf2.AArch64.hv P s₀))).take D →
      bytesAt s'.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D → WP isa (.block rest) s' Q) :
    WP isa (.block (Impl.Pbkdf2.AArch64.digest P D ++ rest)) s Q := by
  have := VG.Proof.Pbkdf2.AArch64.so_le hz; have := VG.Proof.Pbkdf2.AArch64.N_le hz; have := VG.Proof.Pbkdf2.AArch64.B_le hz; have hz_fits := hz.fits; have hz_DN := hz.DN; have hz_NL := hz.NL
  have hz_D4 := hz.D4; have hz_N4 := hz.N4; have hz_pad := hz.pad
  unfold Impl.Pbkdf2.AArch64.digest
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (hs.out s ?_ ?_ ?_) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, m₁⟩ => ?_
  · rw [h.x19]; exact VG.Proof.Pbkdf2.AArch64.in_scr' hz hp h.wr (a := P.so + 56) (n := P.N) (by omega_using [hz_fits])
  · rw [h.x21]; exact VG.Proof.Pbkdf2.AArch64.in_scr hz hp h.wr (by omega_using [hz_NL, hz_fits])
  · rw [h.x19, h.x21]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  rw [h.x21, h.x19] at m₁
  have hdl := H.digest_length (H.stateAt s.mem (VG.Proof.Pbkdf2.AArch64.hv P s₀))
  have f₁ : Frame [⟨VG.Proof.Pbkdf2.AArch64.blk P s₀, P.N⟩] s.mem s₁.mem := by
    rw [m₁]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hdl]; exact Region.contains_self _ _)
  have b₁ : bytesAt s₁.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀) D = (H.digest (H.stateAt s.mem (VG.Proof.Pbkdf2.AArch64.hv P s₀))).take D := by
    rw [bytesAt_take _ _ (Nat.le_of_lt_succ (Nat.lt_succ_of_le hz.DN)), m₁, bytesAt_writeBytes_self' hdl (by omega_using [hz_NL, this])]
  have r₁ : bytesAt s₁.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀ + BitVec.ofNat 64 P.N) (P.B - P.N) =
      bytesAt s.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀ + BitVec.ofNat 64 P.N) (P.B - P.N) := by
    rw [m₁]
    refine bytesAt_writeBytes_sep _ _ ?_ (by omega_using [this])
    have := VG.Proof.Pbkdf2.AArch64.blk_sep P s₀ (a := P.N) (n := P.B - P.N) (b := 0) (k := P.N) (.inr (by omega)) (by omega_using [hz_NL, this]) (by omega_using [hz_NL, this])
      (by omega)
    rw [VG.Proof.Pbkdf2.AArch64.blk0] at this; rw [hdl]; exact this
  have hsplit : ∀ m : Mem, bytesAt m (VG.Proof.Pbkdf2.AArch64.blk P s₀ + BitVec.ofNat 64 D) (P.B - D) =
      bytesAt m (VG.Proof.Pbkdf2.AArch64.blk P s₀ + BitVec.ofNat 64 D) (P.N - D) ++ bytesAt m (VG.Proof.Pbkdf2.AArch64.blk P s₀ + BitVec.ofNat 64 P.N) (P.B - P.N) := by
    intro m
    rw [show P.B - D = (P.N - D) + (P.B - P.N) by omega_using [hz_NL, hz_DN], bytesAt_add, add_ofNat (VG.Proof.Pbkdf2.AArch64.blk P s₀),
      show D + (P.N - D) = P.N by omega_using [hz_DN]]
  have hY : bytesAt s.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀ + BitVec.ofNat 64 P.N) (P.B - P.N) = (H.tailPad D).drop (P.N - D) := by
    rw [← hpad, hsplit, List.drop_left' (bytesAt_length _ _ _)]
  by_cases hDN : D < P.N
  · simp only [hDN, ↓reduceIte]
    refine VG.Proof.Pbkdf2.AArch64.padFrom_ok (a := D) (b := P.N) (by omega) (by omega) (by omega) (by omega_using [hz_NL, this]) (s := s₁) (p := VG.Proof.Pbkdf2.AArch64.blk P s₀)
      (by rw [g₁ _ (by decide), h.x21]) (fun j hj => VG.Proof.Pbkdf2.AArch64.in_blk hz hp (wr₁.trans h.wr) (by omega_using [hj, hz_NL]))
      fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => k s₂ (fun r hr => (g₂ r hr).trans (g₁ r hr)) (rd₂.trans rd₁) (wr₂.trans wr₁)
        (sp₂.trans sp₁) ?_ ?_ ?_
    · rw [m₂]
      refine f₁.trans (VG.WriteBytes.writeBytes_frame _ _ _ ?_)
      simp only [List.length_append, List.length_singleton, List.length_replicate]
      exact Offset.contains_base _ (by omega_using [hDN]) (by omega_using [hz_NL, hz_DN, this])
    · rw [m₂, bytesAt_writeBytes_sep _ _ ?_ (by omega), b₁]
      have := VG.Proof.Pbkdf2.AArch64.blk_sep P s₀ (a := 0) (n := D) (b := D) (k := P.N - D) (.inl (by omega)) (by omega_using [hz_NL, hz_DN, this]) (by omega_using [hz_NL, hz_DN, this])
        (by omega)
      rw [VG.Proof.Pbkdf2.AArch64.blk0] at this
      have e : ([0x80] ++ List.replicate (P.N - D - 1) 0 : List Byte).length = P.N - D := by simp; omega_using [hDN]
      rw [e]; exact this
    · have hfix : [(0x80 : Byte)] ++ List.replicate (P.N - D - 1) 0 = (H.tailPad D).take (P.N - D) :=
        (H.tailPad_take (by omega_using [hDN]) (by omega_using [hz_NL, hz_DN])).symm
      have hfl : ((H.tailPad D).take (P.N - D)).length = P.N - D := by
        rw [List.length_take, H.tailPad_length (by omega_using [hz_pad])]; omega_using [hz_NL]
      rw [hsplit, m₂, hfix, bytesAt_writeBytes_self' hfl (by omega_using [hz_NL, this]),
        bytesAt_writeBytes_sep _ _ ?_ (by omega), r₁, hY, List.take_append_drop]
      have := VG.Proof.Pbkdf2.AArch64.blk_sep P s₀ (a := P.N) (n := P.B - P.N) (b := D) (k := P.N - D) (.inr (by omega_using [hz_DN])) (by omega)
        (by omega) (by omega)
      rw [hfl]; exact this
  · simp only [hDN, ↓reduceIte, List.nil_append]
    obtain rfl : D = P.N := by omega_using [hDN, hz_DN]
    refine k s₁ g₁ rd₁ wr₁ sp₁ f₁ b₁ ?_
    rw [r₁, hY, Nat.sub_self, List.drop_zero]

end

/-! ## A step -/

section
variable (P : Params) (D : Nat) (H : Md P.B P.N P.L) (s₀ : State)

/-- A step, as the code computes it, from the key's inner and outer hash values. -/
abbrev stepM : List Byte → List Byte :=
  H.step D (H.stateAt s₀.mem (VG.Proof.Pbkdf2.AArch64.key s₀)) (H.stateAt s₀.mem (VG.Proof.Pbkdf2.AArch64.key s₀ + BitVec.ofNat 64 (P.N + P.B)))

/-- What the body writes: the compression function's scratch space, the hash
value and the block, and `T`. -/
abbrev bodyR : List Region := [⟨VG.Proof.Pbkdf2.AArch64.scr s₀, P.so⟩, ⟨VG.Proof.Pbkdf2.AArch64.hv P s₀, P.N + P.B⟩, VG.Proof.Pbkdf2.AArch64.tR D s₀]

/-- Our caller's registers and our return address, saved in the scratch space. -/
def SavedAll (m : Mem) : Prop :=
  Saved P.md (VG.Proof.Pbkdf2.AArch64.scr s₀) s₀.gpr m ∧ m.readW (VG.Proof.Pbkdf2.AArch64.scr s₀ + BitVec.ofNat 64 (raO P)) 64 = s₀.gpr .x30

end

/-- The loop invariant, with `r` steps left. -/
structure Inv (P : Params) (D W : Nat) (H : Md P.B P.N P.L) (s₀ : State) (r : Nat) (s : State) : Prop
    extends VG.Proof.Pbkdf2.AArch64.Regs P D W s₀ s where
  x24 : s.gpr .x24 = BitVec.ofNat 64 r
  saved : VG.Proof.Pbkdf2.AArch64.SavedAll P s₀ s.mem
  pad : bytesAt s.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D
  le : r ≤ VG.Proof.Pbkdf2.AArch64.nn s₀
  val : Spec.Pbkdf2.iterate (VG.Proof.Pbkdf2.AArch64.stepM P D H s₀) (VG.Proof.Pbkdf2.AArch64.nn s₀) (bytesAt s₀.mem (VG.Proof.Pbkdf2.AArch64.up s₀) D) (bytesAt s₀.mem (VG.Proof.Pbkdf2.AArch64.tp s₀) D) =
    Spec.Pbkdf2.iterate (VG.Proof.Pbkdf2.AArch64.stepM P D H s₀) r (bytesAt s.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀) D) (bytesAt s.mem (VG.Proof.Pbkdf2.AArch64.tp s₀) D)

section
variable {P : Params} {D W : Nat} (hz : VG.Proof.Pbkdf2.AArch64.Sizes P D W) {s₀ : State} (hp : VG.Proof.Pbkdf2.AArch64.Pre P D W s₀)
include hz hp

/-- The saved registers are outside what the body writes. -/
theorem saved_frame {m m' : Mem} (h : VG.Proof.Pbkdf2.AArch64.SavedAll P s₀ m) (hf : Frame (VG.Proof.Pbkdf2.AArch64.bodyR P D s₀) m m') : VG.Proof.Pbkdf2.AArch64.SavedAll P s₀ m' := by
  have := VG.Proof.Pbkdf2.AArch64.so_le hz; have := VG.Proof.Pbkdf2.AArch64.N_le hz; have := VG.Proof.Pbkdf2.AArch64.B_le hz; have hz_fits := hz.fits
  have rd : ∀ d, P.so ≤ d → d + 8 ≤ P.so + 56 →
      m'.readW (VG.Proof.Pbkdf2.AArch64.scr s₀ + BitVec.ofNat 64 d) 64 = m.readW (VG.Proof.Pbkdf2.AArch64.scr s₀ + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    refine hf.readW (r := ⟨VG.Proof.Pbkdf2.AArch64.scr s₀ + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
    · exact (hp.t_s.sub_right (VG.Proof.Pbkdf2.AArch64.scr_sub s₀ (by omega))).symm
  refine ⟨fun q hq => ?_, ?_⟩
  · have hd := VG.Proof.Pbkdf2.AArch64.saved_off hz hq
    rw [← h.1 q hq]
    exact rd _ hd.1 (by show q.2 + 8 ≤ P.so + 56; omega)
  · rw [← h.2]; exact rd _ (by simp only [raO]; omega) (by simp only [raO]; omega)

omit hz hp in
/-- A range of the scratch space from `hv` on, within what the body writes. -/
theorem sub_body {a n : Nat} (h₁ : P.so + 56 ≤ a) (h₂ : a + n ≤ P.so + 56 + P.N + P.B) :
    ∃ r' ∈ VG.Proof.Pbkdf2.AArch64.bodyR P D s₀, Region.Sub ⟨VG.Proof.Pbkdf2.AArch64.scr s₀ + BitVec.ofNat 64 a, n⟩ r' :=
  ⟨⟨VG.Proof.Pbkdf2.AArch64.hv P s₀, P.N + P.B⟩, by simp, Offset.sub _ h₁ (by omega)⟩

omit hp in
/-- A range of the block disjoint from what the compression and loading the hash value write. -/
theorem blk_disj {a n : Nat} (h : a + n ≤ P.B) :
    ∀ r ∈ [⟨VG.Proof.Pbkdf2.AArch64.hv P s₀, P.N⟩, ⟨VG.Proof.Pbkdf2.AArch64.scr s₀, P.so⟩], Region.Disjoint ⟨VG.Proof.Pbkdf2.AArch64.blk P s₀ + BitVec.ofNat 64 a, n⟩ r := by
  have := VG.Proof.Pbkdf2.AArch64.so_le hz; have := VG.Proof.Pbkdf2.AArch64.N_le hz; have := VG.Proof.Pbkdf2.AArch64.B_le hz; have hz_fits := hz.fits
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [add_ofNat]
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)

/-- Loading the key's hash value at `key + o` and compressing the block into it. -/
theorem lc_ok {H : Md P.B P.N P.L} (hR : H.Reloc) {name : String} {code : Prog isa} (hf : VG.Proof.Pbkdf2.AArch64.CompOk H P.so code)
    {o : Nat} (ho : o + P.N ≤ 2 * (P.N + P.B)) (ho4 : o % 4 = 0) {s : State} (h : VG.Proof.Pbkdf2.AArch64.Regs P D W s₀ s)
    (hpad : bytesAt s.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D) {c : Prog isa}
    {Q : State → Prop}
    (k : ∀ s', VG.Proof.Pbkdf2.AArch64.Regs P D W s₀ s' → s'.gpr .x24 = s.gpr .x24 → Frame (VG.Proof.Pbkdf2.AArch64.bodyR P D s₀) s.mem s'.mem →
      Frame [⟨VG.Proof.Pbkdf2.AArch64.scr s₀, P.so⟩, ⟨VG.Proof.Pbkdf2.AArch64.hv P s₀, P.N⟩] s.mem s'.mem →
      bytesAt s'.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D →
      bytesAt s'.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀) D = bytesAt s.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀) D →
      H.stateAt s'.mem (VG.Proof.Pbkdf2.AArch64.hv P s₀) =
        H.compress (H.stateAt s₀.mem (VG.Proof.Pbkdf2.AArch64.key s₀ + BitVec.ofNat 64 o)) (H.tailBlock D (bytesAt s.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀) D)) →
      WP isa c s' Q) :
    WP isa (.block (loadKey P o)) s fun s' => WP isa (.seq (compressBlock name code) c) s' Q := by
  have := VG.Proof.Pbkdf2.AArch64.so_le hz; have := VG.Proof.Pbkdf2.AArch64.N_le hz; have := VG.Proof.Pbkdf2.AArch64.B_le hz; have hz_fits := hz.fits; have hz_DN := hz.DN; have hz_pad := hz.pad
  have hz_NL := hz.NL
  rw [← List.append_nil (loadKey P o)]
  refine VG.Proof.Pbkdf2.AArch64.load_ok hz hp hR h (o := o) ho ho4 fun s₁ g₁ rd₁ wr₁ sp₁ f₁ e₁ => WP.block_nil ?_
  have h₁ := h.write (fun r hr => g₁ r (VG.Proof.Pbkdf2.AArch64.ne9 r hr)) rd₁ wr₁ sp₁ (VG.Proof.Pbkdf2.AArch64.frame_scr (a := P.so + 56) (by omega_using [hz_fits]) f₁)
  refine WP.seq (VG.Proof.Pbkdf2.AArch64.cmp_ok hz hp hf h₁ fun s₂ h₂ x24₂ f₂ e₂ => ?_)
  have fh₁ : ∀ {a n : Nat}, a + n ≤ P.B → ∀ r ∈ [(⟨VG.Proof.Pbkdf2.AArch64.hv P s₀, P.N⟩ : Region)],
      Region.Disjoint ⟨VG.Proof.Pbkdf2.AArch64.blk P s₀ + BitVec.ofNat 64 a, n⟩ r :=
    fun h' r hr => VG.Proof.Pbkdf2.AArch64.blk_disj hz h' r (by simp at hr; simp [hr])
  have p₁ : bytesAt s₁.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D :=
    (Memory.frame_bytesAt f₁ (fh₁ (by omega)) (by omega_using [this])).trans hpad
  have u₁ : bytesAt s₁.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀) D = bytesAt s.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀) D := by
    have := Memory.frame_bytesAt f₁ (fh₁ (a := 0) (n := D) (by omega_using [hz_pad])) (by omega); rwa [VG.Proof.Pbkdf2.AArch64.blk0] at this
  have u₂ : bytesAt s₂.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀) D = bytesAt s₁.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀) D := by
    have := Memory.frame_bytesAt f₂ (VG.Proof.Pbkdf2.AArch64.blk_disj hz (a := 0) (n := D) (by omega)) (by omega); rwa [VG.Proof.Pbkdf2.AArch64.blk0] at this
  rw [e₁, H.blockAt_eq (by omega) p₁, u₁] at e₂
  have f : Frame [⟨VG.Proof.Pbkdf2.AArch64.scr s₀, P.so⟩, ⟨VG.Proof.Pbkdf2.AArch64.hv P s₀, P.N⟩] s.mem s₂.mem :=
    (f₁.mono (by simp)).trans (f₂.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  refine k s₂ h₂ (x24₂.trans (g₁ _ (by decide))) (f.sub fun r hr => ?_) f
    ((Memory.frame_bytesAt f₂ (VG.Proof.Pbkdf2.AArch64.blk_disj hz (by omega)) (by omega)).trans p₁) (u₂.trans u₁) e₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨⟨VG.Proof.Pbkdf2.AArch64.scr s₀, P.so⟩, by simp, fun _ h => h⟩
  · exact VG.Proof.Pbkdf2.AArch64.sub_body (by omega) (by omega_using [])

/-- The end of a step: the digest into the block, `T ← T ⊕ U` and the count. -/
theorem tail_ok {H : Md P.B P.N P.L} (hs : VG.Proof.Pbkdf2.AArch64.Shape H) {s : State} (h : VG.Proof.Pbkdf2.AArch64.Regs P D W s₀ s)
    (hpad : bytesAt s.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D) {Q : State → Prop}
    (k : ∀ s', VG.Proof.Pbkdf2.AArch64.Regs P D W s₀ s' → s'.gpr .x24 = s.gpr .x24 - BitVec.ofNat 64 1 →
      Frame (VG.Proof.Pbkdf2.AArch64.bodyR P D s₀) s.mem s'.mem →
      bytesAt s'.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D →
      bytesAt s'.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀) D = (H.digest (H.stateAt s.mem (VG.Proof.Pbkdf2.AArch64.hv P s₀))).take D →
      bytesAt s'.mem (VG.Proof.Pbkdf2.AArch64.tp s₀) D =
        Spec.Pbkdf2.xorBytes (bytesAt s.mem (VG.Proof.Pbkdf2.AArch64.tp s₀) D) ((H.digest (H.stateAt s.mem (VG.Proof.Pbkdf2.AArch64.hv P s₀))).take D) → Q s') :
    WP isa (.block (Impl.Pbkdf2.AArch64.digest P D ++ (List.range (D / 4)).flatMap xorW ++
      ([.subImm .x .x24 .x24 1] : List Instr))) s Q := by
  have := VG.Proof.Pbkdf2.AArch64.so_le hz; have := VG.Proof.Pbkdf2.AArch64.N_le hz; have := VG.Proof.Pbkdf2.AArch64.B_le hz; have hz_fits := hz.fits; have hz_DN := hz.DN; have hz_D4 := hz.D4; have hz_W := hz.W
  have hz_pad := hz.pad; have hz_NL := hz.NL
  rw [List.append_assoc]
  refine VG.Proof.Pbkdf2.AArch64.digest_ok hz hp hs h hpad fun s₆ g₆ rd₆ wr₆ sp₆ f₆ b₆ p₆ => ?_
  have h₆ := h.write (fun r hr => g₆ r (VG.Proof.Pbkdf2.AArch64.ne9 r hr)) rd₆ wr₆ sp₆ (VG.Proof.Pbkdf2.AArch64.frame_scr (a := P.so + 56 + P.N) (by omega) f₆)
  have hd : Region.Disjoint (VG.Proof.Pbkdf2.AArch64.tR D s₀) ⟨VG.Proof.Pbkdf2.AArch64.blk P s₀, D⟩ := hp.t_s.sub_right (VG.Proof.Pbkdf2.AArch64.scr_sub s₀ (by omega))
  have hD4 : 4 * (D / 4) = D := by omega
  refine VG.Proof.Pbkdf2.AArch64.xor_ok hd (by omega_using [hz_pad, this]) (D / 4) (by omega_using []) _ s₆ _ h₆.x21 h₆.x23
    (fun j hj => by
      obtain ⟨r, hr, hc⟩ := VG.Proof.Pbkdf2.AArch64.in_blk hz hp h₆.wr (a := 4 * j) (n := 4) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (fun j hj => ⟨VG.Proof.Pbkdf2.AArch64.tR D s₀, by simp [h₆.wr, hp.wr], Offset.contains_base _ (by omega) (by omega)⟩)
    fun s₇ g₇ rd₇ wr₇ sp₇ m₇ => ?_
  rw [hD4] at m₇
  have hxl : (Spec.Pbkdf2.xorBytes (bytesAt s₆.mem (VG.Proof.Pbkdf2.AArch64.tp s₀) D) (bytesAt s₆.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀) D)).length = D := by
    rw [Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
  have f₇ : Frame [VG.Proof.Pbkdf2.AArch64.tR D s₀] s₆.mem s₇.mem := by
    rw [m₇]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
  have h₇ := h₆.write (fun r hr => g₇ r (VG.Proof.Pbkdf2.AArch64.ne9 r hr) (VG.Proof.Pbkdf2.AArch64.ne10 r hr)) rd₇ wr₇ sp₇ (f₇.mono (by simp))
  refine wp_subImm (by decide) fun s₈ u₈ => WP.block_nil ?_
  have h₈ := h₇.write (fun r hr => u₈.other r (VG.Proof.Pbkdf2.AArch64.ne24 r hr)) u₈.rd u₈.wr u₈.sp (by rw [u₈.mem]; exact Frame.refl _ _)
  have x24₇ : s₇.gpr .x24 = s.gpr .x24 := by rw [g₇ _ (by decide) (by decide), g₆ _ (by decide)]
  have hT₆ : bytesAt s₆.mem (VG.Proof.Pbkdf2.AArch64.tp s₀) D = bytesAt s.mem (VG.Proof.Pbkdf2.AArch64.tp s₀) D :=
    Memory.frame_bytesAt f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.t_s.sub_right (VG.Proof.Pbkdf2.AArch64.scr_sub s₀ (a := P.so + 56 + P.N) (n := P.N) (by omega))) (by omega_using [hz_W, hz_DN, hz_fits])
  refine k s₈ h₈ (by rw [u₈.gpr, x24₇]) ?_ ?_ ?_ ?_
  · rw [u₈.mem]
    refine (f₆.sub fun r hr => ?_).trans (f₇.mono (by simp))
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Proof.Pbkdf2.AArch64.sub_body (by omega) (by omega_using [hz_NL])
  · rw [u₈.mem]
    exact (Memory.frame_bytesAt f₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.t_s.sub_right (by rw [add_ofNat]; exact VG.Proof.Pbkdf2.AArch64.scr_sub s₀ (by omega_using [hz_pad, hz_fits]))).symm) (by omega_using [this])).trans p₆
  · rw [u₈.mem, m₇, bytesAt_writeBytes_sep _ _ (hd.symm.sep (Region.contains_self _ _) (by
      rw [hxl]; exact Region.contains_self _ _)) (by omega_using [hz_W, hz_DN, hz_fits]), b₆]
  · rw [u₈.mem, m₇, bytesAt_writeBytes_self' hxl (by omega), hT₆, b₆]

omit hz hp in
theorem iterate_succ (f : List Byte → List Byte) (n : Nat) (u t : List Byte) :
    Spec.Pbkdf2.iterate f (n + 1) u t = Spec.Pbkdf2.iterate f n (f u) (Spec.Pbkdf2.xorBytes t (f u)) := rfl

theorem body_ok {H : Md P.B P.N P.L} (hs : VG.Proof.Pbkdf2.AArch64.Shape H) (hR : H.Reloc) {name : String} {code : Prog isa}
    (hf : VG.Proof.Pbkdf2.AArch64.CompOk H P.so code) {r : Nat} {s : State} (h : VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀ (r + 1) s) :
    WP isa (body P D name code) s fun s' =>
      eval (.nonzero .x .x24) s' = some (r != 0) ∧ VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀ r s' := by
  have := VG.Proof.Pbkdf2.AArch64.so_le hz; have := VG.Proof.Pbkdf2.AArch64.N_le hz; have := VG.Proof.Pbkdf2.AArch64.B_le hz; have hz_fits := hz.fits; have hz_DN := hz.DN; have hz_pad := hz.pad
  have hz_NL := hz.NL
  unfold body
  refine WP.seq (VG.Proof.Pbkdf2.AArch64.lc_ok hz hp hR hf (o := 0) (by omega_using []) rfl h.toRegs h.pad fun s₂ h₂ x24₂ f₂ g₂ p₂ _ e₂ => ?_)
  refine WP.seq (VG.Proof.Pbkdf2.AArch64.digest_ok hz hp hs h₂ p₂ fun s₃ g₃ rd₃ wr₃ sp₃ f₃ b₃ p₃ => ?_)
  have h₃ := h₂.write (fun r hr => g₃ r (VG.Proof.Pbkdf2.AArch64.ne9 r hr)) rd₃ wr₃ sp₃ (VG.Proof.Pbkdf2.AArch64.frame_scr (a := P.so + 56 + P.N) (by omega) f₃)
  refine VG.Proof.Pbkdf2.AArch64.lc_ok hz hp hR hf (o := P.N + P.B) (by omega) (by have hz_N4 := hz.N4; rcases hz.B with h | h <;> omega) h₃ p₃ fun s₅ h₅ x24₅ f₅ g₅ p₅ _ e₅ => ?_
  refine VG.Proof.Pbkdf2.AArch64.tail_ok hz hp hs h₅ p₅ fun s₈ h₈ x24₈ f₈ p₈ b₈ t₈ => ?_
  rw [e₅, b₃, e₂, VG.Proof.Pbkdf2.AArch64.add0] at b₈ t₈
  have x24₅' : s₅.gpr .x24 = BitVec.ofNat 64 (r + 1) := by
    rw [x24₅, g₃ _ (by decide), x24₂, h.x24]
  have hlt : r + 1 < 2 ^ 64 := by
    have h_le := h.le; have := ((s₀.gpr .x2).setWidth 32).isLt; simp at *; omega_using [h_le]
  have e₈ : s₅.gpr .x24 - BitVec.ofNat 64 1 = BitVec.ofNat 64 r := by
    rw [x24₅', show BitVec.ofNat 64 1 = 1 from rfl, ofNat_pred (by omega)]; rfl
  have fb : Frame (VG.Proof.Pbkdf2.AArch64.bodyR P D s₀) s.mem s₈.mem :=
    ((f₂.trans (f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Pbkdf2.AArch64.sub_body (by omega) (by omega))).trans f₅).trans f₈
  have hT₅ : bytesAt s₅.mem (VG.Proof.Pbkdf2.AArch64.tp s₀) D = bytesAt s.mem (VG.Proof.Pbkdf2.AArch64.tp s₀) D := by
    refine Memory.frame_bytesAt (rs := [⟨VG.Proof.Pbkdf2.AArch64.scr s₀, P.so⟩, ⟨VG.Proof.Pbkdf2.AArch64.hv P s₀, P.N + P.B⟩])
      (((g₂.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)).trans (g₅.sub fun r hr => ?_)) (fun r hr => ?_) (by omega)
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    · rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨VG.Proof.Pbkdf2.AArch64.hv P s₀, P.N + P.B⟩, by simp, Region.sub_prefix (by omega)⟩
    · subst hr; exact ⟨⟨VG.Proof.Pbkdf2.AArch64.hv P s₀, P.N + P.B⟩, by simp, Offset.sub _ (by omega) (by omega)⟩
    · rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨VG.Proof.Pbkdf2.AArch64.hv P s₀, P.N + P.B⟩, by simp, Region.sub_prefix (by omega)⟩
    · rcases hr with rfl | rfl
      · exact hp.t_s.sub_right (Region.sub_prefix (by omega))
      · exact hp.t_s.sub_right (VG.Proof.Pbkdf2.AArch64.scr_sub s₀ (by omega_using [hz_fits]))
  rw [hT₅] at t₈
  refine ⟨?_, h₈, by rw [x24₈, e₈], VG.Proof.Pbkdf2.AArch64.saved_frame hz hp h.saved fb, p₈, by have h_le := h.le; omega, ?_⟩
  · simp only [eval_nonzero, x24₈, e₈, bne, ofNat_beq_zero (by omega : r < 2 ^ 64)]
    cases r <;> rfl
  · rw [h.val, VG.Proof.Pbkdf2.AArch64.iterate_succ, b₈, t₈]; rfl

theorem loop_ok {H : Md P.B P.N P.L} (hs : VG.Proof.Pbkdf2.AArch64.Shape H) (hR : H.Reloc) {name : String} {code : Prog isa}
    (hf : VG.Proof.Pbkdf2.AArch64.CompOk H P.so code) {n : Nat} {s : State} (h : VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀ n s) :
    WP isa (.ite (.zero .x .x24) (.block []) (.loop (body P D name code) (.nonzero .x .x24))) s
      (VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀ 0) := by
  have hlt : n < 2 ^ 64 := by
    have h_le := h.le; have := ((s₀.gpr .x2).setWidth 32).isLt; simp at *; omega
  refine WP.ite (decide (n = 0)) (by change eval (.zero .x .x24) s = _; rw [eval_zero, h.x24, ofNat_beq_zero hlt]) (fun hb => ?_) (fun hb => ?_)
  · obtain rfl : n = 0 := by simpa using hb
    exact WP.block_nil h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hb; omega⟩
    refine WP.loop (fun m s => VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀ (m + 1) s)
      (fun m s hs' => WP.mono (VG.Proof.Pbkdf2.AArch64.body_ok hz hp hs hR hf hs') fun s' ⟨he, hi⟩ => ?_) m s h
    cases m with
    | zero => exact .inl ⟨he, hi⟩
    | succ m => exact .inr ⟨he, m, by omega, hi⟩

end

/-! ## The prologue -/

/-- The memory after saving our caller's registers and our return address. -/
def saveAll (P : Params) (s₀ : State) : Mem :=
  (saveMem P.md s₀.mem (VG.Proof.Pbkdf2.AArch64.scr s₀) s₀.gpr).writeW (VG.Proof.Pbkdf2.AArch64.scr s₀ + BitVec.ofNat 64 (raO P)) (s₀.gpr .x30)

/-- The state after the first instruction, which zero-extends `n`. -/
def zext (s : State) : State := s.write .w .x2 (s.read .w .x2 + BitVec.ofNat 32 0)

theorem zext_exec (s : State) : exec (.addImm .w .x2 .x2 0) s = some (VG.Proof.Pbkdf2.AArch64.zext s) := rfl

theorem zext_upd (s : State) : Upd s (VG.Proof.Pbkdf2.AArch64.zext s) .x2 (((s.gpr .x2).setWidth 32).setWidth 64) := by
  have := Upd.write s .w .x2 (s.read .w .x2 + BitVec.ofNat 32 0)
  simpa [VG.Proof.Pbkdf2.AArch64.zext, State.read, Size.bits] using this

theorem zext_x2 (s : State) : (VG.Proof.Pbkdf2.AArch64.zext s).gpr .x2 = BitVec.ofNat 64 (VG.Proof.Pbkdf2.AArch64.nn s) := by
  rw [(VG.Proof.Pbkdf2.AArch64.zext_upd s).gpr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, VG.Proof.Pbkdf2.AArch64.nn]

/-- After saving our caller's registers and our return address and setting
up our registers. -/
structure Setup (P : Params) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  x19 : s.gpr .x19 = VG.Proof.Pbkdf2.AArch64.hv P s₀
  x20 : s.gpr .x20 = VG.Proof.Pbkdf2.AArch64.scr s₀
  x21 : s.gpr .x21 = VG.Proof.Pbkdf2.AArch64.blk P s₀
  x23 : s.gpr .x23 = VG.Proof.Pbkdf2.AArch64.tp s₀
  x24 : s.gpr .x24 = BitVec.ofNat 64 (VG.Proof.Pbkdf2.AArch64.nn s₀)
  x0 : s.gpr .x0 = VG.Proof.Pbkdf2.AArch64.key s₀
  x1 : s.gpr .x1 = VG.Proof.Pbkdf2.AArch64.up s₀
  cs : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  mem : s.mem = VG.Proof.Pbkdf2.AArch64.saveAll P s₀

section
variable {P : Params} {D W : Nat} (hz : VG.Proof.Pbkdf2.AArch64.Sizes P D W) {s₀ : State} (hp : VG.Proof.Pbkdf2.AArch64.Pre P D W s₀)
include hz hp

theorem setup_ok {rest : List Instr} {Q : State → Prop} (k : ∀ s, VG.Proof.Pbkdf2.AArch64.Setup P s₀ s → WP isa (.block rest) s Q) :
    WP isa (.block (save P.md .x4 ++
      ([.str .x .x30 .x4 (raO P), .addImm .x .x19 .x4 (hvO P), mov .x20 .x4, .addImm .x .x21 .x4 (blkO P),
        mov .x23 .x3, mov .x24 .x2] : List Instr) ++ rest)) (VG.Proof.Pbkdf2.AArch64.zext s₀) Q := by
  have := VG.Proof.Pbkdf2.AArch64.so_le hz; have := VG.Proof.Pbkdf2.AArch64.N_le hz; have := VG.Proof.Pbkdf2.AArch64.B_le hz; have hz_fits := hz.fits; have hz_W := hz.W; have := VG.Proof.Pbkdf2.AArch64.so8 hz
  have u := VG.Proof.Pbkdf2.AArch64.zext_upd s₀
  have zg : ∀ r, r ≠ .x2 → (VG.Proof.Pbkdf2.AArch64.zext s₀).gpr r = s₀.gpr r := u.other
  simp only [List.append_assoc]
  refine save_ok hz.dims (b := .x4) (fun d h₁ h₂ => by
    rw [zg _ (by decide), u.wr]; exact VG.Proof.Pbkdf2.AArch64.in_scr hz hp rfl (by have := VG.Proof.Pbkdf2.AArch64.md_so P; omega_using [this, h₂, hz_fits]))
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_str (a := VG.Proof.Pbkdf2.AArch64.scr s₀ + BitVec.ofNat 64 (raO P)) ⟨by simp only [raO]; omega, by simp only [raO]; omega⟩
    (by rw [g₁, zg _ (by decide)]) (by rw [wr₁, u.wr]; exact VG.Proof.Pbkdf2.AArch64.in_scr hz hp rfl (by simp only [raO]; omega_using [hz_fits]))
    fun s₂ g₂ => ?_
  refine wp_addImm (by simp only [hvO]; omega) fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_addImm (by simp only [blkO]; omega) fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ => ?_
  have G : ∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x23 → r ≠ .x24 → s₇.gpr r = s₁.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₇.other r h5, u₆.other r h4, u₅.other r h3, u₄.other r h2, u₃.other r h1, g₂.gpr]
  have g0 : ∀ r, r ≠ .x2 → s₁.gpr r = s₀.gpr r := fun r h => by rw [g₁, zg r h]
  refine k s₇ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, g₂.rd, rd₁, u.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, wr₁, u.wr]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      g₂.gpr, g0 _ (by decide), hvO]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      g₂.gpr, g0 _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      g₂.gpr, g0 _ (by decide), blkO]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      g₂.gpr, g0 _ (by decide)]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      g₂.gpr, g₁, VG.Proof.Pbkdf2.AArch64.zext_x2]
  · rw [G _ (by decide) (by decide) (by decide) (by decide) (by decide), g0 _ (by decide)]
  · rw [G _ (by decide) (by decide) (by decide) (by decide) (by decide), g0 _ (by decide)]
  · have : r ≠ .x19 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x23 ∧ r ≠ .x24 ∧ r ≠ .x2 := by
      simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [G r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2.1, g0 r this.2.2.2.2.2]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, g₂.sp, sp₁, u.sp]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, g₂.mem, m₁, g₁, zg _ (by decide), zg _ (by decide), u.mem, VG.Proof.Pbkdf2.AArch64.saveAll]
    congr 1

omit hp in
theorem saveAll_frame : Frame [⟨VG.Proof.Pbkdf2.AArch64.scr s₀, P.so + 56⟩] s₀.mem (VG.Proof.Pbkdf2.AArch64.saveAll P s₀) := by
  have := VG.Proof.Pbkdf2.AArch64.so8 hz
  refine ((saveMem_frame hz.dims s₀.mem (VG.Proof.Pbkdf2.AArch64.scr s₀) s₀.gpr).sub fun r hr => ?_).writeW (List.mem_singleton_self _) _
    (Offset.contains_base _ (by simp only [raO]; omega) (by simp only [raO]; omega))
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by have := VG.Proof.Pbkdf2.AArch64.md_so P; omega_using [this])⟩

omit hp in
theorem saveAll_saved : VG.Proof.Pbkdf2.AArch64.SavedAll P s₀ (VG.Proof.Pbkdf2.AArch64.saveAll P s₀) := by
  have := VG.Proof.Pbkdf2.AArch64.so8 hz
  refine ⟨fun q hq => ?_, Mem.readW_writeW_self64 _ _ _⟩
  have hd := VG.Proof.Pbkdf2.AArch64.saved_off hz hq
  rw [VG.Proof.Pbkdf2.AArch64.saveAll, Mem.readW_writeW_sep (Offset.sep _ (.inl (by simp only [raO]; omega_using [hd]))
    (by omega) (by simp only [raO]; omega)) (by decide)]
  exact saveMem_saved hz.dims _ _ _ q hq

/-- Writing `U`, the padding and the length field into the block. -/
theorem fill_ok {H : Md P.B P.N P.L} (hs : VG.Proof.Pbkdf2.AArch64.Shape H) (hok : H.lenOk (P.B + D)) {s : State}
    (h : VG.Proof.Pbkdf2.AArch64.Setup P s₀ s) :
    WP isa (.block ((List.range (D / 4)).flatMap (Impl.Pbkdf2.AArch64.cp32 .x1 .x21 0 0) ++
      Impl.Pbkdf2.AArch64.padLen P D ++ ([mov .x22 .x0] : List Instr))) s (VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀ (VG.Proof.Pbkdf2.AArch64.nn s₀)) := by
  have := VG.Proof.Pbkdf2.AArch64.so_le hz; have := VG.Proof.Pbkdf2.AArch64.N_le hz; have := VG.Proof.Pbkdf2.AArch64.B_le hz; have hz_fits := hz.fits; have hz_DN := hz.DN; have hz_pad := hz.pad
  have hz_NL := hz.NL; have hz_D4 := hz.D4; have hz_L4 := hz.L4; have hz_W := hz.W; have := VG.Proof.Pbkdf2.AArch64.B_ge hz
  have : P.B % 4 = 0 := by rcases hz.B with h | h <;> omega
  have hD4 : 4 * (D / 4) = D := by omega
  simp only [List.append_assoc]
  refine VG.Proof.Pbkdf2.AArch64.copy32_ok (by decide) (by decide) 0 0 (D / 4) ⟨rfl, by omega⟩ ⟨rfl, by omega⟩ _ s _
    (fun j hj => ?_) (fun j hj => ?_) ?_ fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  · rw [h.x1, h.rd, hp.rd, VG.Proof.Pbkdf2.AArch64.add0]
    exact ⟨VG.Proof.Pbkdf2.AArch64.uR D s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [h.x21, VG.Proof.Pbkdf2.AArch64.blk0]; exact VG.Proof.Pbkdf2.AArch64.in_blk hz hp h.wr (by omega_using [hj, hz_pad])
  · rw [h.x1, h.x21, VG.Proof.Pbkdf2.AArch64.blk0, VG.Proof.Pbkdf2.AArch64.add0, hD4]
    exact hp.u_s.sep (Region.contains_self _ _) (Offset.contains_base _ (by omega_using [hz_pad, hz_fits]) (by omega_using [hz_W, hz_fits]))
  rw [h.x21, h.x1, VG.Proof.Pbkdf2.AArch64.blk0, VG.Proof.Pbkdf2.AArch64.add0, hD4] at m₁
  refine VG.Proof.Pbkdf2.AArch64.padLen_ok hs hok hz.D4 hz.L4 this (by omega) (by omega) (s := s₁) (p := VG.Proof.Pbkdf2.AArch64.blk P s₀)
    (by rw [g₁ _ (by decide), h.x21])
    (by rw [g₁ _ (by decide), h.x19, add_ofNat, add_ofNat,
      show P.so + 56 + (P.N + P.B - P.L) = P.so + 56 + P.N + (P.B - P.L) by omega_using [hz_pad]])
    (fun a n h' => VG.Proof.Pbkdf2.AArch64.in_blk hz hp (wr₁.trans h.wr) h') fun s₄ g₄ rd₄ wr₄ sp₄ f₄ p₄ u₄ => ?_
  refine wp_mov fun s₅ u₅ => WP.block_nil ?_
  have hG : ∀ r ∈ VG.Proof.Pbkdf2.AArch64.kept, r ≠ .x22 → s₅.gpr r = s.gpr r := fun r hr h2 => by
    rw [u₅.other r h2, g₄ r (VG.Proof.Pbkdf2.AArch64.ne9 r hr) (VG.Proof.Pbkdf2.AArch64.ne12 r hr) h2, g₁ r (VG.Proof.Pbkdf2.AArch64.ne9 r hr)]
  have f₁ : Frame [⟨VG.Proof.Pbkdf2.AArch64.blk P s₀, P.B⟩] s.mem s₁.mem := by
    rw [m₁]; refine VG.WriteBytes.writeBytes_frame _ _ _ ?_
    rw [bytesAt_length]
    have := Offset.contains_base (VG.Proof.Pbkdf2.AArch64.blk P s₀) (d := 0) (n := D) (k := P.B) (by omega_using [hz_pad]) (by omega)
    rwa [VG.Proof.Pbkdf2.AArch64.blk0] at this
  have fM : Frame [⟨VG.Proof.Pbkdf2.AArch64.blk P s₀, P.B⟩] s.mem s₅.mem := by
    rw [u₅.mem]; exact f₁.trans f₄
  have fB : Frame (VG.Proof.Pbkdf2.AArch64.bodyR P D s₀) s.mem s₅.mem := fM.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Pbkdf2.AArch64.sub_body (by omega) (by omega)
  have fS : Frame [VG.Proof.Pbkdf2.AArch64.tR D s₀, VG.Proof.Pbkdf2.AArch64.scR W s₀] s₀.mem s.mem := by
    rw [h.mem]; exact VG.Proof.Pbkdf2.AArch64.saveAll_frame hz |>.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Pbkdf2.AArch64.scR W s₀, by simp, Region.sub_prefix (by omega_using [hz_fits])⟩
  refine ⟨⟨by rw [u₅.rd, rd₄, rd₁, h.rd], by rw [u₅.wr, wr₄, wr₁, h.wr],
    by rw [hG _ (by decide) (by decide), h.x19], by rw [hG _ (by decide) (by decide), h.x20],
    by rw [hG _ (by decide) (by decide), h.x21],
    by rw [u₅.gpr, g₄ _ (by decide) (by decide) (by decide), g₁ _ (by decide), h.x0],
    by rw [hG _ (by decide) (by decide), h.x23],
    fun r hr => by rw [hG _ (VG.Proof.Pbkdf2.AArch64.untouched_kept r hr) (VG.Proof.Pbkdf2.AArch64.untouched_ne22 r hr), h.cs r hr],
    by rw [u₅.sp, sp₄, sp₁, h.sp],
    fS.trans (VG.Proof.Pbkdf2.AArch64.frame_scr (a := P.so + 56 + P.N) (by omega) fM)⟩,
    by rw [u₅.other _ (by decide), g₄ _ (by decide) (by decide) (by decide), g₁ _ (by decide), h.x24],
    VG.Proof.Pbkdf2.AArch64.saved_frame hz hp (h.mem ▸ VG.Proof.Pbkdf2.AArch64.saveAll_saved hz) fB, by rw [u₅.mem]; exact p₄, Nat.le_refl _, ?_⟩
  · -- `U` and `T`.
    have hU : bytesAt s₅.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀) D = bytesAt s₀.mem (VG.Proof.Pbkdf2.AArch64.up s₀) D := by
      rw [u₅.mem, u₄, m₁, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega), h.mem]
      refine Memory.frame_bytesAt (VG.Proof.Pbkdf2.AArch64.saveAll_frame hz) (fun r hr => ?_) (by omega_using [hz_W, hz_DN, hz_fits])
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.u_s.sub_right (Region.sub_prefix (by omega))
    have hT : bytesAt s₅.mem (VG.Proof.Pbkdf2.AArch64.tp s₀) D = bytesAt s₀.mem (VG.Proof.Pbkdf2.AArch64.tp s₀) D := by
      refine Memory.frame_bytesAt ((VG.Proof.Pbkdf2.AArch64.saveAll_frame hz).mono
        (rs' := [⟨VG.Proof.Pbkdf2.AArch64.scr s₀, P.so + 56⟩, ⟨VG.Proof.Pbkdf2.AArch64.blk P s₀, P.B⟩]) (by simp) |>.trans
        ((h.mem ▸ fM).mono (by simp))) (fun r hr => ?_) (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.t_s.sub_right (Region.sub_prefix (by omega))
      · exact hp.t_s.sub_right (VG.Proof.Pbkdf2.AArch64.scr_sub s₀ (by omega))
    rw [hU, hT]

theorem prologue_ok {H : Md P.B P.N P.L} (hs : VG.Proof.Pbkdf2.AArch64.Shape H) (hok : H.lenOk (P.B + D)) :
    WP isa (.block (prologue P D)) (VG.Proof.Pbkdf2.AArch64.zext s₀) (VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀ (VG.Proof.Pbkdf2.AArch64.nn s₀)) := by
  have := VG.Proof.Pbkdf2.AArch64.setup_ok hz hp (rest := (List.range (D / 4)).flatMap (Impl.Pbkdf2.AArch64.cp32 .x1 .x21 0 0) ++
    Impl.Pbkdf2.AArch64.padLen P D ++ [mov .x22 .x0]) fun s h => VG.Proof.Pbkdf2.AArch64.fill_ok hz hp hs hok h
  unfold prologue
  simpa only [List.append_assoc] using this

omit hz hp in
/-- The final `T` is PBKDF2's, for a key as the contract requires. -/
theorem post_eq {H : Md P.B P.N P.L} {S : StreamingHash} {iv : H.HV} (hl : H.Link S iv D) {m : Mem}
    (hT : bytesAt m (VG.Proof.Pbkdf2.AArch64.tp s₀) D =
      Spec.Pbkdf2.iterate (VG.Proof.Pbkdf2.AArch64.stepM P D H s₀) (VG.Proof.Pbkdf2.AArch64.nn s₀) (bytesAt s₀.mem (VG.Proof.Pbkdf2.AArch64.up s₀) D) (bytesAt s₀.mem (VG.Proof.Pbkdf2.AArch64.tp s₀) D))
    {k0 : List Byte} (hk : k0.length = S.H.blockSize) (hi : S.Repr s₀.mem (VG.Proof.Pbkdf2.AArch64.key s₀) (xorPad k0 ipad))
    (ho : S.Repr s₀.mem (VG.Proof.Pbkdf2.AArch64.key s₀ + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad)) :
    bytesAt m (VG.Proof.Pbkdf2.AArch64.tp s₀) S.digestBytes =
      Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) (VG.Proof.Pbkdf2.AArch64.nn s₀) (bytesAt s₀.mem (VG.Proof.Pbkdf2.AArch64.up s₀) S.digestBytes)
        (bytesAt s₀.mem (VG.Proof.Pbkdf2.AArch64.tp s₀) S.digestBytes) := by
  have hB : 0 < P.B := by have hl_DL := hl.DL; omega
  rw [hl.hB] at hk
  rw [hl.hS] at ho
  have li : (xorPad k0 ipad).length = P.B := by simp [xorPad, hk]
  have lo : (xorPad k0 opad).length = P.B := by simp [xorPad, hk]
  have ei := Md.stateAt_of_repr hB li (hl.repr _ _ _ hi)
  have eo := Md.stateAt_of_repr hB lo (hl.repr _ _ _ ho)
  rw [hl.hD]
  refine hT.trans (Md.iterate_congr (fun u hu => ?_) (fun u => Md.step_length H hl.DN _ _ u) _ _ _
    (bytesAt_length _ _ _)).symm
  rw [Md.hmac_step hl hk hu, ei, eo]

theorem epilogue_ok {H : Md P.B P.N P.L} {S : StreamingHash} {iv : H.HV} (hl : H.Link S iv D) {s : State}
    (h : VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀ 0 s) :
    WP isa (.block (epilogue P)) s fun s' => GprAbi s₀ s' ∧ (VG.Proof.Pbkdf2.AArch64.iterK S W).post s₀ s' := by
  have := VG.Proof.Pbkdf2.AArch64.so_le hz; have := VG.Proof.Pbkdf2.AArch64.N_le hz; have := VG.Proof.Pbkdf2.AArch64.B_le hz; have hz_fits := hz.fits; have hz_W := hz.W; have := VG.Proof.Pbkdf2.AArch64.so8 hz
  unfold epilogue
  refine wp_ldr (a := VG.Proof.Pbkdf2.AArch64.scr s₀ + BitVec.ofNat 64 (raO P)) ⟨by simp only [raO]; omega, by simp only [raO]; omega⟩
    (by rw [h.x20]) (VG.Proof.Pbkdf2.AArch64.in_scr' hz hp h.wr (by simp only [raO]; omega)) fun s₁ u₁ => ?_
  refine restore_ok hz.dims (scr := VG.Proof.Pbkdf2.AArch64.scr s₀) (by rw [u₁.other _ (by decide), h.x20])
    (fun d _ hd₂ => by rw [u₁.rd, u₁.wr]; exact VG.Proof.Pbkdf2.AArch64.in_scr' hz hp h.wr (by have := VG.Proof.Pbkdf2.AArch64.md_so P; omega))
    s₀.gpr (by rw [u₁.mem]; exact h.saved.1)
    fun s' hsv hother hmem _ _ hsp => ⟨⟨fun r hr => ?_, by rw [hsp, u₁.sp, h.sp]⟩, fun k0 hk hi ho => ?_⟩
  · by_cases h30 : r = .x30
    · subst h30; rw [hother _ (by simp [saved]), u₁.gpr, h.saved.2]
    · refine preserved_of (P := P.md) hsv (fun r hr => ?_) r hr h30
      rw [hother r (VG.Proof.Pbkdf2.AArch64.untouched_not_saved _ r hr), u₁.other r (VG.Proof.Pbkdf2.AArch64.untouched_ne30 r hr),
        h.cs r hr]
  · rw [hmem, u₁.mem]; exact VG.Proof.Pbkdf2.AArch64.post_eq hl h.val.symm hk hi ho

end

/-! ## Correctness -/

/-- What the proof needs of a hash function, with its code's `Params`, a
`D`-byte digest and `W` words of scratch space: the sizes, the length field
and digest of its code, that its hash value depends only on the bytes it is
stored in, that the length field of a `B + D`-byte message is its byte
count's, and that it is the hash function `S` of the specification. -/
structure HashOk (P : Params) (D W : Nat) (S : StreamingHash) (H : Md P.B P.N P.L) (iv : H.HV) : Prop where
  sizes : VG.Proof.Pbkdf2.AArch64.Sizes P D W
  shape : VG.Proof.Pbkdf2.AArch64.Shape H
  reloc : H.Reloc
  lenOk : H.lenOk (P.B + D)
  link : H.Link S iv D

theorem main_ok {P : Params} {D W : Nat} {S : StreamingHash} {H : Md P.B P.N P.L} {iv : H.HV}
    (ho : VG.Proof.Pbkdf2.AArch64.HashOk P D W S H iv) {name : String} {code : Prog isa} (hf : VG.Proof.Pbkdf2.AArch64.CompOk H P.so code) {s₀ : State}
    (hp : VG.Proof.Pbkdf2.AArch64.Pre P D W s₀) :
    WP isa (main P D name code) (VG.Proof.Pbkdf2.AArch64.zext s₀) fun s' => GprAbi s₀ s' ∧ (VG.Proof.Pbkdf2.AArch64.iterK S W).post s₀ s' := by
  unfold main
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.AArch64.prologue_ok ho.sizes hp ho.shape ho.lenOk) fun s₁ h => ?_)
  exact WP.seq (WP.mono (VG.Proof.Pbkdf2.AArch64.loop_ok ho.sizes hp ho.shape ho.reloc hf h) fun s₂ h₂ =>
    VG.Proof.Pbkdf2.AArch64.epilogue_ok ho.sizes hp ho.link h₂)

/-- `padLen` writes no SIMD register. -/
theorem padLen_keepsV {P : Params} {D : Nat} {H : Md P.B P.N P.L} (hs : VG.Proof.Pbkdf2.AArch64.Shape H) :
    (Impl.Pbkdf2.AArch64.padLen P D).all keepsV = true := by
  simp [Impl.Pbkdf2.AArch64.padLen, padFrom, keepsV, vdstOf, hs.lenKeepsV]

/-- The wrapper adds scalar instructions and checked length/digest code. -/
theorem iterate_keepsV {P : Params} {D : Nat} {H : Md P.B P.N P.L}
    (hs : VG.Proof.Pbkdf2.AArch64.Shape H) {name : String} {code : Prog isa} (hc : code.allInstrs keepsV = true) :
    (iterate P D name code).allInstrs keepsV = true := by
  rw [Code.allInstrs_eq] at hc ⊢
  by_cases hDN : D < P.N <;>
  simp [iterate, main, prologue, epilogue, body, loadKey, compressBlock,
    Impl.Pbkdf2.AArch64.digest, padFrom, Impl.Pbkdf2.AArch64.cp32, xorW, Impl.MdStream.AArch64.compressAt,
    Impl.MdStream.AArch64.compressWith, Impl.MdStream.AArch64.save,
    Impl.MdStream.AArch64.saved, Impl.MdStream.AArch64.restore, Impl.MdStream.AArch64.mov,
    instrs, keepsV, vdstOf, hc, VG.Proof.Pbkdf2.AArch64.padLen_keepsV hs, hs.outKeepsV, hDN]

theorem correct {P : Params} {D W : Nat} {S : StreamingHash} {H : Md P.B P.N P.L} {iv : H.HV}
    (ho : VG.Proof.Pbkdf2.AArch64.HashOk P D W S H iv) {name : String} {code : Prog isa} (hf : VG.Proof.Pbkdf2.AArch64.CompOk H P.so code) {s₀ : State}
    (hp : VG.Proof.Pbkdf2.AArch64.Pre P D W s₀) :
    WP isa (iterate P D name code) s₀ fun s' => abiPreserved s₀ s' ∧ (VG.Proof.Pbkdf2.AArch64.iterK S W).post s₀ s' :=
  WP.withPreservedV
    (WP.seq (MdStream.AArch64.WP.cons (VG.Proof.Pbkdf2.AArch64.zext_exec s₀) (WP.block_nil (VG.Proof.Pbkdf2.AArch64.main_ok ho hf hp))))
    (VG.Proof.Pbkdf2.AArch64.iterate_keepsV ho.shape hf.keepsV)

/-- `iterate` is correct and keeps what the calling convention requires. -/
theorem iterate_ok {P : Params} {D W : Nat} {S : StreamingHash} {H : Md P.B P.N P.L} {iv : H.HV}
    (ho : VG.Proof.Pbkdf2.AArch64.HashOk P D W S H iv) {name : String} {code : Prog isa} (hf : VG.Proof.Pbkdf2.AArch64.CompOk H P.so code)
    (s : State) (hs : (VG.Proof.Pbkdf2.AArch64.iterK S W).pre s) :
    ∃ t s', Exec isa (iterate P D name code) s t s' ∧ abiPreserved s s' ∧ (VG.Proof.Pbkdf2.AArch64.iterK S W).post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.Pbkdf2.AArch64.correct ho hf (VG.Proof.Pbkdf2.AArch64.pre_of ho.link.hS ho.link.hD hs)
  exact ⟨t, s', he, h⟩

end VG.Proof.Pbkdf2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.AArch64.IterateCT`. -/
section

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on AArch64: constant time

As on x86-64 (`Proof/Pbkdf2/X86_64/IterateCT.lean`): this holds for any
compression function (`CompOk`), so it is proven once for every
implementation. The taint analysis cannot prove it without looking into the
compression function, so we relate two runs (`RelCT`): at every point,
correctness determines our registers from the public arguments alone, so they
agree; between the calls, the taint analysis proves each block constant time
from that (`Checks`, evaluated for each hash function, since the code depends
on its sizes); and the calls are constant time by the compression function's
own proof (`compressAt_rel`).
-/

namespace VG.Proof.Pbkdf2.AArch64

open VG VG.AArch64
open VG.Impl.Pbkdf2.AArch64 (Params loadKey xorW compressBlock body prologue epilogue main iterate)
open VG.Impl.MdStream.AArch64 (mov)
open VG.Proof.MdStream (Md)
open VG.Proof.MdStream.AArch64 (wp_mov eval_zero ofNat_beq_zero)
open VG.Spec.Sha256 (bytesAt)
open VG.Spec.Hmac (StreamingHash)

/-- The registers the blocks between the calls use. -/
abbrev regsS : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24]

/-- The taint checks of the pieces of `iterate` between its calls, which
depend on the hash function's sizes, its length field and its digest. -/
structure Checks (P : Params) (D : Nat) : Prop where
  ext : ∃ hc, (taint.check (Taint.ofRegs []) (.block [.addImm .w .x2 .x2 0]) hc).isSome = true
  pro : ∃ hc, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) (.block (prologue P D)) hc).isSome = true
  load : ∃ hc, (taint.check (Taint.ofRegs VG.Proof.Pbkdf2.AArch64.regsS) (.block (loadKey P 0)) hc).isSome = true
  arg : ∃ hc, (taint.check (Taint.ofRegs VG.Proof.Pbkdf2.AArch64.regsS) (.block [mov .x1 .x21]) hc).isSome = true
  mid : ∃ hc, (taint.check (Taint.ofRegs VG.Proof.Pbkdf2.AArch64.regsS)
    (.block (Impl.Pbkdf2.AArch64.digest P D ++ loadKey P (P.N + P.B))) hc).isSome = true
  fin : ∃ hc, (taint.check (Taint.ofRegs VG.Proof.Pbkdf2.AArch64.regsS) (.block (Impl.Pbkdf2.AArch64.digest P D ++
    (List.range (D / 4)).flatMap xorW ++ [.subImm .x .x24 .x24 1])) hc).isSome = true
  epi : ∃ hc, (taint.check (Taint.ofRegs [.x20]) (.block (epilogue P)) hc).isSome = true
  ite : ∃ hc, (taint.check (Taint.ofRegs []) (.block []) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  x0 : s₀.gpr .x0 = s₀'.gpr .x0
  x1 : s₀.gpr .x1 = s₀'.gpr .x1
  x2 : (s₀.gpr .x2).setWidth 32 = (s₀'.gpr .x2).setWidth 32
  x3 : s₀.gpr .x3 = s₀'.gpr .x3
  x4 : s₀.gpr .x4 = s₀'.gpr .x4
  sp : s₀.sp = s₀'.sp

theorem PubEq.nn {s₀ s₀' : State} (hq : VG.Proof.Pbkdf2.AArch64.PubEq s₀ s₀') : VG.Proof.Pbkdf2.AArch64.nn s₀ = VG.Proof.Pbkdf2.AArch64.nn s₀' :=
  congrArg BitVec.toNat hq.x2

/-- Agreement on `rs` and the stack pointer. -/
theorem agree_of {rs : List Reg} {s s' : State} (hsp : s.sp = s'.sp) (h : ∀ r ∈ rs, s.gpr r = s'.gpr r) :
    AArch64.Taint.Agree (AArch64.Taint.ofRegs rs) s s' :=
  ⟨hsp, fun r hr => h r (AArch64.Taint.mem_ofRegs.mp hr)⟩

/-- The state during a step, with `v` in `x24`. -/
structure St (P : Params) (D W : Nat) (H : Md P.B P.N P.L) (s₀ : State) (v : Addr) (s : State) : Prop
    extends VG.Proof.Pbkdf2.AArch64.Regs P D W s₀ s where
  x24 : s.gpr .x24 = v
  pad : bytesAt s.mem (VG.Proof.Pbkdf2.AArch64.blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D

section
variable {P : Params} {D W : Nat} {H : Md P.B P.N P.L}

/-- The registers the blocks use agree in two runs. -/
theorem St.agree {s₀ s₀' : State} (hq : VG.Proof.Pbkdf2.AArch64.PubEq s₀ s₀') {v : Addr} {s s' : State} (h : VG.Proof.Pbkdf2.AArch64.St P D W H s₀ v s)
    (h' : VG.Proof.Pbkdf2.AArch64.St P D W H s₀' v s') : AArch64.Taint.Agree (AArch64.Taint.ofRegs VG.Proof.Pbkdf2.AArch64.regsS) s s' := by
  refine VG.Proof.Pbkdf2.AArch64.agree_of (by rw [h.sp, h'.sp, hq.sp]) fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.x19, h'.x19, VG.Proof.Pbkdf2.AArch64.hv, VG.Proof.Pbkdf2.AArch64.hv, VG.Proof.Pbkdf2.AArch64.scr, VG.Proof.Pbkdf2.AArch64.scr, hq.x4]
  · rw [h.x20, h'.x20, VG.Proof.Pbkdf2.AArch64.scr, VG.Proof.Pbkdf2.AArch64.scr, hq.x4]
  · rw [h.x21, h'.x21, VG.Proof.Pbkdf2.AArch64.blk, VG.Proof.Pbkdf2.AArch64.blk, VG.Proof.Pbkdf2.AArch64.scr, VG.Proof.Pbkdf2.AArch64.scr, hq.x4]
  · rw [h.x22, h'.x22, VG.Proof.Pbkdf2.AArch64.key, VG.Proof.Pbkdf2.AArch64.key, hq.x0]
  · rw [h.x23, h'.x23, VG.Proof.Pbkdf2.AArch64.tp, VG.Proof.Pbkdf2.AArch64.tp, hq.x3]
  · rw [h.x24, h'.x24]

theorem St.of_inv {s₀ : State} {r : Nat} {s : State} (h : VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀ (r + 1) s) :
    VG.Proof.Pbkdf2.AArch64.St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s :=
  ⟨h.toRegs, h.x24, h.pad⟩

variable (hz : VG.Proof.Pbkdf2.AArch64.Sizes P D W) {s₀ : State} (hp : VG.Proof.Pbkdf2.AArch64.Pre P D W s₀) {v : Addr}
include hz hp

/-! ## What each piece of a step does, in one run -/

theorem load_st (hR : H.Reloc) {o : Nat} (ho : o + P.N ≤ 2 * (P.N + P.B)) (ho4 : o % 4 = 0) {s : State}
    (h : VG.Proof.Pbkdf2.AArch64.St P D W H s₀ v s) :
    WP isa (.block (loadKey P o)) s (VG.Proof.Pbkdf2.AArch64.St P D W H s₀ v) := by
  have := VG.Proof.Pbkdf2.AArch64.so_le hz; have := VG.Proof.Pbkdf2.AArch64.N_le hz; have := VG.Proof.Pbkdf2.AArch64.B_le hz; have := hz.fits; have := hz.DN; have := hz.pad
  have := hz.NL
  rw [← List.append_nil (loadKey P o)]
  exact VG.Proof.Pbkdf2.AArch64.load_ok hz hp hR h.toRegs ho ho4 fun s' g rd wr sp f _ => WP.block_nil
    ⟨h.toRegs.write (fun r hr => g r (VG.Proof.Pbkdf2.AArch64.ne9 r hr)) rd wr sp (VG.Proof.Pbkdf2.AArch64.frame_scr (a := P.so + 56) (by omega) f),
      (g _ (by decide)).trans h.x24,
      (Memory.frame_bytesAt f (fun r hr => VG.Proof.Pbkdf2.AArch64.blk_disj hz (by omega) r (by simp at hr; simp [hr])) (by omega)).trans
        h.pad⟩

theorem cmp_st {name : String} {code : Prog isa} (hf : VG.Proof.Pbkdf2.AArch64.CompOk H P.so code) {s : State} (h : VG.Proof.Pbkdf2.AArch64.St P D W H s₀ v s) :
    WP isa (compressBlock name code) s (VG.Proof.Pbkdf2.AArch64.St P D W H s₀ v) := by
  have := VG.Proof.Pbkdf2.AArch64.so_le hz; have := VG.Proof.Pbkdf2.AArch64.N_le hz; have := VG.Proof.Pbkdf2.AArch64.B_le hz; have := hz.fits; have := hz.DN; have := hz.pad
  have := hz.NL
  exact VG.Proof.Pbkdf2.AArch64.cmp_ok hz hp hf h.toRegs fun s' h' x24 f _ =>
    ⟨h', x24.trans h.x24, (Memory.frame_bytesAt f (VG.Proof.Pbkdf2.AArch64.blk_disj hz (by omega)) (by omega)).trans h.pad⟩

theorem mid_st (hs : VG.Proof.Pbkdf2.AArch64.Shape H) (hR : H.Reloc) {s : State} (h : VG.Proof.Pbkdf2.AArch64.St P D W H s₀ v s) :
    WP isa (.block (Impl.Pbkdf2.AArch64.digest P D ++ loadKey P (P.N + P.B))) s (VG.Proof.Pbkdf2.AArch64.St P D W H s₀ v) := by
  have := VG.Proof.Pbkdf2.AArch64.so_le hz; have := VG.Proof.Pbkdf2.AArch64.N_le hz; have := VG.Proof.Pbkdf2.AArch64.B_le hz; have := hz.fits; have := hz.NL; have := hz.N4
  refine VG.Proof.Pbkdf2.AArch64.digest_ok hz hp hs h.toRegs h.pad fun s' g rd wr sp f _ p => ?_
  exact VG.Proof.Pbkdf2.AArch64.load_st hz hp hR (by omega) (by rcases hz.B with h | h <;> omega)
    ⟨h.toRegs.write (fun r hr => g r (VG.Proof.Pbkdf2.AArch64.ne9 r hr)) rd wr sp (VG.Proof.Pbkdf2.AArch64.frame_scr (a := P.so + 56 + P.N) (by omega) f),
      (g _ (by decide)).trans h.x24, p⟩

/-! ## Two runs -/

variable {s₀' : State} (hp' : VG.Proof.Pbkdf2.AArch64.Pre P D W s₀') (hq : VG.Proof.Pbkdf2.AArch64.PubEq s₀ s₀')
include hp' hq

theorem cmp_rel {name : String} {code : Prog isa} (hf : VG.Proof.Pbkdf2.AArch64.CompOk H P.so code) (hc : VG.Proof.Pbkdf2.AArch64.Checks P D) :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.AArch64.St P D W H s₀ v s ∧ VG.Proof.Pbkdf2.AArch64.St P D W H s₀' v s') (compressBlock name code) fun s s' =>
      VG.Proof.Pbkdf2.AArch64.St P D W H s₀ v s ∧ VG.Proof.Pbkdf2.AArch64.St P D W H s₀' v s' := by
  obtain ⟨_, ha⟩ := hc.arg
  have mv : ∀ {s₀ : State}, VG.Proof.Pbkdf2.AArch64.Pre P D W s₀ → ∀ {s : State}, VG.Proof.Pbkdf2.AArch64.St P D W H s₀ v s →
      WP isa (.block [mov .x1 .x21]) s fun s => VG.Proof.Pbkdf2.AArch64.St P D W H s₀ v s ∧ s.gpr .x1 = VG.Proof.Pbkdf2.AArch64.blk P s₀ :=
    by intro _ _ _ h; exact wp_mov fun s₁ u₁ => WP.block_nil ⟨⟨h.toRegs.write (fun r hr => u₁.other r (VG.Proof.Pbkdf2.AArch64.ne1 r hr)) u₁.rd u₁.wr
      u₁.sp (by rw [u₁.mem]; exact Frame.refl _ _), (u₁.other _ (by decide)).trans h.x24,
      by rw [u₁.mem]; exact h.pad⟩, by rw [u₁.gpr, h.x21]⟩
  have su : RelCT isa (fun s s' => VG.Proof.Pbkdf2.AArch64.St P D W H s₀ v s ∧ VG.Proof.Pbkdf2.AArch64.St P D W H s₀' v s') (.block [mov .x1 .x21])
      fun s s' => (VG.Proof.Pbkdf2.AArch64.St P D W H s₀ v s ∧ s.gpr .x1 = VG.Proof.Pbkdf2.AArch64.blk P s₀) ∧ (VG.Proof.Pbkdf2.AArch64.St P D W H s₀' v s' ∧ s'.gpr .x1 = VG.Proof.Pbkdf2.AArch64.blk P s₀') :=
    ((RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Pbkdf2.AArch64.regsS) (fun _ _ h => St.agree hq h.1 h.2) ha).wp
      fun _ _ h => ⟨mv hp h.1, mv hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have call := VG.Proof.Pbkdf2.AArch64.compressAt_rel (H := H) hf (name := name) (st := VG.Proof.Pbkdf2.AArch64.hv P s₀) (scr := VG.Proof.Pbkdf2.AArch64.scr s₀) (src := VG.Proof.Pbkdf2.AArch64.blk P s₀)
    (P' := fun s s' => (VG.Proof.Pbkdf2.AArch64.St P D W H s₀ v s ∧ s.gpr .x1 = VG.Proof.Pbkdf2.AArch64.blk P s₀) ∧ (VG.Proof.Pbkdf2.AArch64.St P D W H s₀' v s' ∧ s'.gpr .x1 = VG.Proof.Pbkdf2.AArch64.blk P s₀'))
    fun s s' ⟨⟨h, hsi⟩, ⟨h', hsi'⟩⟩ => by
      have e : VG.Proof.Pbkdf2.AArch64.hv P s₀' = VG.Proof.Pbkdf2.AArch64.hv P s₀ ∧ VG.Proof.Pbkdf2.AArch64.scr s₀' = VG.Proof.Pbkdf2.AArch64.scr s₀ ∧ VG.Proof.Pbkdf2.AArch64.blk P s₀' = VG.Proof.Pbkdf2.AArch64.blk P s₀ := by
        refine ⟨?_, ?_, ?_⟩ <;> simp only [VG.Proof.Pbkdf2.AArch64.hv, VG.Proof.Pbkdf2.AArch64.blk, VG.Proof.Pbkdf2.AArch64.scr, hq.x4]
      have c' := VG.Proof.Pbkdf2.AArch64.callOk_of hz hp' h'.toRegs hsi'
      rw [e.1, e.2.1, e.2.2] at c'
      exact ⟨VG.Proof.Pbkdf2.AArch64.callOk_of hz hp h.toRegs hsi, c', by rw [h.sp, h'.sp, hq.sp]⟩
  exact ((su.seq call).wp fun _ _ h => ⟨VG.Proof.Pbkdf2.AArch64.cmp_st hz hp hf h.1, VG.Proof.Pbkdf2.AArch64.cmp_st hz hp' hf h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem body_rel (hs : VG.Proof.Pbkdf2.AArch64.Shape H) (hR : H.Reloc) {name : String} {code : Prog isa} (hf : VG.Proof.Pbkdf2.AArch64.CompOk H P.so code)
    (hc : VG.Proof.Pbkdf2.AArch64.Checks P D) {r : Nat} :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀ (r + 1) s ∧ VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀' (r + 1) s') (body P D name code)
      fun s s' => (eval (.nonzero .x .x24) s = some (r != 0) ∧ VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀ r s) ∧
        (eval (.nonzero .x .x24) s' = some (r != 0) ∧ VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀' r s') := by
  have := VG.Proof.Pbkdf2.AArch64.so_le hz; have := VG.Proof.Pbkdf2.AArch64.N_le hz; have := VG.Proof.Pbkdf2.AArch64.B_le hz
  obtain ⟨_, hl⟩ := hc.load
  obtain ⟨_, hm⟩ := hc.mid
  obtain ⟨_, hfi⟩ := hc.fin
  have l0 : RelCT isa (fun s s' => VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀ (r + 1) s ∧ VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀' (r + 1) s') (.block (loadKey P 0))
      fun s s' => VG.Proof.Pbkdf2.AArch64.St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s ∧ VG.Proof.Pbkdf2.AArch64.St P D W H s₀' (BitVec.ofNat 64 (r + 1)) s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Pbkdf2.AArch64.regsS) (fun _ _ h =>
      St.agree hq (St.of_inv h.1) (St.of_inv h.2)) hl).wp
      fun _ _ h => ⟨VG.Proof.Pbkdf2.AArch64.load_st hz hp hR (by omega) rfl (St.of_inv h.1),
        VG.Proof.Pbkdf2.AArch64.load_st hz hp' hR (by omega) rfl (St.of_inv h.2)⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have dl : RelCT isa (fun s s' => VG.Proof.Pbkdf2.AArch64.St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s ∧
        VG.Proof.Pbkdf2.AArch64.St P D W H s₀' (BitVec.ofNat 64 (r + 1)) s')
      (.block (Impl.Pbkdf2.AArch64.digest P D ++ loadKey P (P.N + P.B)))
      fun s s' => VG.Proof.Pbkdf2.AArch64.St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s ∧ VG.Proof.Pbkdf2.AArch64.St P D W H s₀' (BitVec.ofNat 64 (r + 1)) s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Pbkdf2.AArch64.regsS) (fun _ _ h => St.agree hq h.1 h.2)
      hm).wp fun _ _ h => ⟨VG.Proof.Pbkdf2.AArch64.mid_st hz hp hs hR h.1, VG.Proof.Pbkdf2.AArch64.mid_st hz hp' hs hR h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have fin : RelCT isa (fun s s' => VG.Proof.Pbkdf2.AArch64.St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s ∧
        VG.Proof.Pbkdf2.AArch64.St P D W H s₀' (BitVec.ofNat 64 (r + 1)) s')
      (.block (Impl.Pbkdf2.AArch64.digest P D ++ (List.range (D / 4)).flatMap xorW ++ [.subImm .x .x24 .x24 1]))
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Pbkdf2.AArch64.regsS) (fun _ _ h => St.agree hq h.1 h.2) hfi
  have c := VG.Proof.Pbkdf2.AArch64.cmp_rel hz hp hp' hq (v := BitVec.ofNat 64 (r + 1)) hf hc (name := name)
  exact ((l0.seq (c.seq (dl.seq (c.seq fin)))).wp fun _ _ h =>
    ⟨VG.Proof.Pbkdf2.AArch64.body_ok hz hp hs hR hf h.1, VG.Proof.Pbkdf2.AArch64.body_ok hz hp' hs hR hf h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

theorem loop_rel (hs : VG.Proof.Pbkdf2.AArch64.Shape H) (hR : H.Reloc) {name : String} {code : Prog isa} (hf : VG.Proof.Pbkdf2.AArch64.CompOk H P.so code)
    (hc : VG.Proof.Pbkdf2.AArch64.Checks P D) {n : Nat} :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀ (n + 1) s ∧ VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀' (n + 1) s')
      (.loop (body P D name code) (.nonzero .x .x24)) fun _ _ => True :=
  RelCT.loop (M := isa) (body := body P D name code) (c := .nonzero .x .x24) (Q := fun _ _ => True)
    (fun m s s' => VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀ (m + 1) s ∧ VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀' (m + 1) s') (fun m => by
      intro s s' t t' u u' h e e'
      obtain ⟨ht, ⟨z, i⟩, ⟨z', i'⟩⟩ := VG.Proof.Pbkdf2.AArch64.body_rel hz hp hp' hq hs hR hf hc _ _ _ _ _ _ h e e'
      refine ⟨ht, z.trans z'.symm, fun _ => trivial, fun hc' => ?_⟩
      have hc'' : some (m != 0) = some true := z.symm.trans hc'
      cases m with
      | zero => cases hc''
      | succ m => exact ⟨m, by omega, i, i'⟩) n

theorem main_rel {S : StreamingHash} {iv : H.HV} (ho : VG.Proof.Pbkdf2.AArch64.HashOk P D W S H iv) {name : String}
    {code : Prog isa} (hf : VG.Proof.Pbkdf2.AArch64.CompOk H P.so code) (hc : VG.Proof.Pbkdf2.AArch64.Checks P D) :
    RelCT isa (fun s s' => s = VG.Proof.Pbkdf2.AArch64.zext s₀ ∧ s' = VG.Proof.Pbkdf2.AArch64.zext s₀') (main P D name code) fun _ _ => True := by
  obtain ⟨_, hpr⟩ := hc.pro
  obtain ⟨_, hep⟩ := hc.epi
  obtain ⟨_, hit⟩ := hc.ite
  have hlt : ∀ {s₀ : State}, VG.Proof.Pbkdf2.AArch64.nn s₀ < 2 ^ 64 := fun {s₀} => by
    have := ((s₀.gpr .x2).setWidth 32).isLt; simp only [VG.Proof.Pbkdf2.AArch64.nn]; omega
  have pro : RelCT isa (fun s s' => s = VG.Proof.Pbkdf2.AArch64.zext s₀ ∧ s' = VG.Proof.Pbkdf2.AArch64.zext s₀') (.block (prologue P D)) fun s s' =>
      VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀ (VG.Proof.Pbkdf2.AArch64.nn s₀) s ∧ VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀' (VG.Proof.Pbkdf2.AArch64.nn s₀') s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
      (P := fun s s' => s = VG.Proof.Pbkdf2.AArch64.zext s₀ ∧ s' = VG.Proof.Pbkdf2.AArch64.zext s₀') (fun _ _ ⟨e, e'⟩ => by
        subst e e'
        refine VG.Proof.Pbkdf2.AArch64.agree_of (by rw [(VG.Proof.Pbkdf2.AArch64.zext_upd _).sp, (VG.Proof.Pbkdf2.AArch64.zext_upd _).sp, hq.sp]) fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [(VG.Proof.Pbkdf2.AArch64.zext_upd _).other _ (by decide), (VG.Proof.Pbkdf2.AArch64.zext_upd _).other _ (by decide), hq.x0]
        · rw [(VG.Proof.Pbkdf2.AArch64.zext_upd _).other _ (by decide), (VG.Proof.Pbkdf2.AArch64.zext_upd _).other _ (by decide), hq.x1]
        · rw [VG.Proof.Pbkdf2.AArch64.zext_x2, VG.Proof.Pbkdf2.AArch64.zext_x2, hq.nn]
        · rw [(VG.Proof.Pbkdf2.AArch64.zext_upd _).other _ (by decide), (VG.Proof.Pbkdf2.AArch64.zext_upd _).other _ (by decide), hq.x3]
        · rw [(VG.Proof.Pbkdf2.AArch64.zext_upd _).other _ (by decide), (VG.Proof.Pbkdf2.AArch64.zext_upd _).other _ (by decide), hq.x4]) hpr).wp
      fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨VG.Proof.Pbkdf2.AArch64.prologue_ok hz hp ho.shape ho.lenOk, VG.Proof.Pbkdf2.AArch64.prologue_ok hz hp' ho.shape ho.lenOk⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have br : RelCT isa (fun s s' => VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀ (VG.Proof.Pbkdf2.AArch64.nn s₀) s ∧ VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀' (VG.Proof.Pbkdf2.AArch64.nn s₀') s')
      (.ite (.zero .x .x24) (.block []) (.loop (body P D name code) (.nonzero .x .x24)))
      fun s s' => VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀ 0 s ∧ VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀' 0 s' := by
    refine (RelCT.ite (fun s s' h => ?_) (RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ h => VG.Proof.Pbkdf2.AArch64.agree_of (by rw [h.1.1.sp, h.1.2.sp, hq.sp]) (by simp)) hit) ?_).wp
      (fun _ _ h => ⟨VG.Proof.Pbkdf2.AArch64.loop_ok hz hp ho.shape ho.reloc hf h.1, VG.Proof.Pbkdf2.AArch64.loop_ok hz hp' ho.shape ho.reloc hf h.2⟩)
      |>.mono (fun _ _ h => h) fun _ _ h => h.2
    · show eval (.zero .x .x24) s = eval (.zero .x .x24) s'
      rw [eval_zero, eval_zero, h.1.x24, h.2.x24, hq.nn]
    · intro s s' t t' u u' ⟨⟨i, i'⟩, hc'⟩ e e'
      have z : eval (.zero .x .x24) s = some (decide (VG.Proof.Pbkdf2.AArch64.nn s₀ = 0)) := by
        rw [eval_zero, i.x24, ofNat_beq_zero hlt]
      have hc'' : some (decide (VG.Proof.Pbkdf2.AArch64.nn s₀ = 0)) = some false := z.symm.trans hc'
      have hne : VG.Proof.Pbkdf2.AArch64.nn s₀ ≠ 0 := fun h0 => by rw [h0] at hc''; cases hc''
      obtain ⟨m, hm⟩ : ∃ m, VG.Proof.Pbkdf2.AArch64.nn s₀ = m + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero hne).symm⟩
      rw [hm] at i
      rw [← hq.nn, hm] at i'
      exact VG.Proof.Pbkdf2.AArch64.loop_rel hz hp hp' hq ho.shape ho.reloc hf hc _ _ _ _ _ _ ⟨i, i'⟩ e e'
  have epi : RelCT isa (fun s s' => VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀ 0 s ∧ VG.Proof.Pbkdf2.AArch64.Inv P D W H s₀' 0 s') (.block (epilogue P))
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.x20]) (fun _ _ h => VG.Proof.Pbkdf2.AArch64.agree_of (by rw [h.1.sp, h.2.sp, hq.sp])
      fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.1.x20, h.2.x20, VG.Proof.Pbkdf2.AArch64.scr, VG.Proof.Pbkdf2.AArch64.scr, hq.x4]) hep
  exact pro.seq (br.seq epi)

theorem iterate_rel {S : StreamingHash} {iv : H.HV} (ho : VG.Proof.Pbkdf2.AArch64.HashOk P D W S H iv) {name : String}
    {code : Prog isa} (hf : VG.Proof.Pbkdf2.AArch64.CompOk H P.so code) (hc : VG.Proof.Pbkdf2.AArch64.Checks P D) :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (iterate P D name code) fun _ _ => True := by
  obtain ⟨_, hex⟩ := hc.ext
  have ext : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block [.addImm .w .x2 .x2 0])
      fun s s' => s = VG.Proof.Pbkdf2.AArch64.zext s₀ ∧ s' = VG.Proof.Pbkdf2.AArch64.zext s₀' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ ⟨e, e'⟩ => VG.Proof.Pbkdf2.AArch64.agree_of (by rw [e, e', hq.sp])
      (by simp)) hex).wp (F₁ := fun s => s = VG.Proof.Pbkdf2.AArch64.zext s₀) (F₂ := fun s => s = VG.Proof.Pbkdf2.AArch64.zext s₀')
      fun _ _ ⟨e, e'⟩ => by
        subst e e'
        exact ⟨MdStream.AArch64.WP.cons (VG.Proof.Pbkdf2.AArch64.zext_exec _) (WP.block_nil rfl),
          MdStream.AArch64.WP.cons (VG.Proof.Pbkdf2.AArch64.zext_exec _) (WP.block_nil rfl)⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  exact ext.seq (VG.Proof.Pbkdf2.AArch64.main_rel hz hp hp' hq ho hf hc)

end

/-! ## Verified -/

theorem pubEq_of {S : StreamingHash} {W : Nat} {s₁ s₂ : State} (h : (VG.Proof.Pbkdf2.AArch64.iterK S W).pub s₁ s₂) : VG.Proof.Pbkdf2.AArch64.PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- `iterate` is verified against `iterK`, for any hash function the proof
supports (`HashOk`), whose pieces of code the taint analysis accepts
(`Checks`), and any compression function (`CompOk`). -/
theorem verified {P : Params} {D W : Nat} {S : StreamingHash} {H : Md P.B P.N P.L} {iv : H.HV}
    (ho : VG.Proof.Pbkdf2.AArch64.HashOk P D W S H iv) (hc : VG.Proof.Pbkdf2.AArch64.Checks P D) {name : String} {code : Prog isa} (hf : VG.Proof.Pbkdf2.AArch64.CompOk H P.so code)
    (hsat : ∃ s, (VG.Proof.Pbkdf2.AArch64.iterK S W).pre s) :
    Verified AArch64.target (iterate P D name code) (VG.Proof.Pbkdf2.AArch64.iterK S W) := by
  refine ⟨VG.Proof.Pbkdf2.AArch64.iterate_ok ho hf, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  exact (VG.Proof.Pbkdf2.AArch64.iterate_rel ho.sizes (VG.Proof.Pbkdf2.AArch64.pre_of ho.link.hS ho.link.hD h₁) (VG.Proof.Pbkdf2.AArch64.pre_of ho.link.hS ho.link.hD h₂)
    (VG.Proof.Pbkdf2.AArch64.pubEq_of hpub) ho hf hc _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- `iterK` implies the shared contract, for any hash function and scratch
space, given that the shared contract is satisfiable. -/
theorem iterImp (S : StreamingHash) (W : Nat) (h : ∃ s, (Spec.Pbkdf2.iterateContract S W AArch64.abi).pre s) :
    (VG.Proof.Pbkdf2.AArch64.iterK S W).Implies (Spec.Pbkdf2.iterateContract S W AArch64.abi) := by
  generic_implies [
    Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, VG.Proof.Pbkdf2.AArch64.iterK, AArch64.abi, AArch64.argRegs] using h

/-- A state satisfying `iterate`'s precondition, with states of `S` bytes, a
digest of `D` bytes and `8 W` bytes of scratch space. -/
def iterSat (S D W : Nat) : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x1 => 0x20000 | .x3 => 0x30000 | .x4 => 0x40000
    | _ => 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x10000, 2 * S⟩, ⟨0x20000, D⟩]
  wr := [⟨0x30000, D⟩, ⟨0x40000, 8 * W⟩]

end VG.Proof.Pbkdf2.AArch64

end
