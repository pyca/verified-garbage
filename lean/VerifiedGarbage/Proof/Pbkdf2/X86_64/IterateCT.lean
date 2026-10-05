import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Impl.Pbkdf2.X86_64
import VerifiedGarbage.Proof.Pbkdf2.MdKeys
import VerifiedGarbage.Proof.Pbkdf2.MdKeys
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Hmac.Generic.Implies

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.X86_64.Copy`. -/
section

/-!
# PBKDF2-HMAC's iteration on x86-64: copying words

What `n` copies of a 32-bit word (`cp32`, `Impl/Pbkdf2/X86_64.lean`) write.
-/

namespace VG.Proof.Pbkdf2.X86_64

open VG VG.X86_64
open VG.Impl.MdStream.X86_64 (at_)
open VG.Impl.Pbkdf2.X86_64 (cp32)
open VG.Proof.MdStream.X86_64 (ea_at ofInt_natCast wp_mov32m wp_store32)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil)
open VG.Proof.Hmac.Common (copy_mem bytesAt_zero)
open VG.Spec.Sha256 (bytesAt)

theorem ea_off (s : State) (b : Reg) (o j : Nat) :
    s.ea (at_ b (o + j)) = s.gpr b + BitVec.ofNat 64 o + BitVec.ofNat 64 j := by
  rw [ea_at, ofInt_natCast, BitVec.ofNat_add, BitVec.add_assoc]

/-- `n` copies of 32-bit words write the `4 n` bytes at `src + o₁` to `dst + o₂`. -/
theorem copy32_ok {src dst : Reg} (hs : src ≠ .rax) (hd : dst ≠ .rax) (o₁ o₂ : Nat) (n : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * k)) 4) →
    Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) (4 * n) (s.gpr dst + BitVec.ofNat 64 o₂) (4 * n) →
    4 * n < 2 ^ 64 →
    (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = VG.WriteBytes.writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (4 * n)) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (cp32 src dst o₁ o₂) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by rw [Nat.mul_zero, bytesAt_zero, VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro rest s Q hin hout hsep hlt k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      (fun x hx hy => hsep x (by omega) (by omega)) (by omega) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [cp32, List.cons_append, List.nil_append]
    refine wp_mov32m (a := s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * n))
      (by rw [VG.Proof.Pbkdf2.X86_64.ea_off, g₁ _ hs]) (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_store32 (a := s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * n))
      (by rw [VG.Proof.Pbkdf2.X86_64.ea_off, u₂.other _ hd, g₁ _ hd]) (by rw [u₂.wr, wr₁]; exact hout n (by omega))
      fun s₃ g₃ m₃ rd₃ wr₃ => k s₃ (fun r hr => by rw [g₃, u₂.other r hr, g₁ r hr])
        (by rw [rd₃, u₂.rd, rd₁]) (by rw [wr₃, u₂.wr, wr₁]) ?_
    rw [m₃, u₂.gpr, u₂.mem, m₁, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq,
      Nat.mul_succ]
    exact copy_mem s.mem _ _ n 4 (by rwa [← Nat.mul_succ]) (by omega)

end VG.Proof.Pbkdf2.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.X86_64.Iterate`. -/
section

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on x86-64

The iteration (`Impl/Pbkdf2/X86_64.lean`) is correct for any hash function the
generic streaming proofs describe (`Md`), whose code stores the length field
and writes the digest as `Shape` says, with any correct compression function
(`CalleeOk`), used as a black box through its proof; `Md.hmac_step` says that
its two compressions per step compute HMAC.
-/

namespace VG.Proof.Pbkdf2.X86_64

open VG VG.X86_64
open VG.Impl.MdStream.X86_64 (Params at_ save restore saved)
open VG.Impl.Pbkdf2.X86_64 (hvO blkO loadKey padFrom xorW compressBlock body prologue iterate)
open VG.Proof.MdStream (Md)
open VG.Proof.MdStream.X86_64 (Dims Shape CalleeOk CallOk compressAt_ok Upd wp_mov wp_mov32i wp_addi wp_subi
  wp_test wp_mov32m wp_store32 wp_store wp_movm ea_at ofInt_natCast Saved saveMem saveMem_saved saveMem_frame
  saved_offset save_eq restore_eq sx_ofNat zx_ofNat ofNat_pred ofNat_beq_zero add_ofNat setWidth32)
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame writeBytes_append)
open VG.Proof.Hmac.Common (bytesAt_add bytesAt_length bytesAt_writeBytes_sep bytesAt_writeBytes_self
  writeBytes_at bytesAt_getD')
open VG.Proof.Hmac.Generic.Common (bytesAt_take bytesAt_writeBytes_self')
open VG.Spec.Hmac (StreamingHash xorPad ipad opad hmacBlockKey)

/-! ## The contract -/

/-- The contract the proof is written against: `VG.Spec.Pbkdf2.iterateContract`
of the streaming hash function `S` with `W` words of scratch space, on
x86-64, with the 8 bytes of stack below the return address that the calls
of the compression function use. -/
def iterK (S : StreamingHash) (W : Nat) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 2 * S.stateBytes⟩
    let u : Region := ⟨s.gpr .rsi, S.digestBytes⟩
    let t : Region := ⟨s.gpr .rcx, S.digestBytes⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * W⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [key, u] ∧ s.wr = [t, scratch] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch ∧
    ret.Disjoint key ∧ ret.Disjoint u ∧ ret.Disjoint t ∧ ret.Disjoint scratch ∧
    stack.Disjoint key ∧ stack.Disjoint u ∧ stack.Disjoint t ∧ stack.Disjoint scratch ∧
    (s.gpr .rdi).toNat + 2 * S.stateBytes ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8 * W ≤ 2 ^ 64
  post s s' := ∀ k0, k0.length = S.H.blockSize →
    S.Repr s.mem (s.gpr .rdi) (xorPad k0 ipad) →
    S.Repr s.mem (s.gpr .rdi + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .rcx) S.digestBytes =
      Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) ((s.gpr .rdx).setWidth 32).toNat
        (bytesAt s.mem (s.gpr .rsi) S.digestBytes) (bytesAt s.mem (s.gpr .rcx) S.digestBytes)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32 ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- The sizes the proof supports, checked for each hash function by `decide`:
words of 4 bytes, a digest of at most the hash value, room for the padding
in the block after the digest and after the hash value, and room in the
scratch space for the compression function's, our caller's registers, the
hash value and the block. -/
structure Sizes (P : Params) (D W : Nat) : Prop where
  dims : Dims P
  N4 : P.N % 4 = 0
  D4 : D % 4 = 0
  L4 : P.L % 4 = 0
  D0 : 0 < D
  DN : D ≤ P.N
  NL : P.N + P.L ≤ P.B
  pad : D + 4 ≤ P.B - P.L
  fits : P.so + 48 + P.N + P.B ≤ 8 * W
  W : W ≤ 1024

/-! ## The precondition -/

section
variable (P : Params) (D W : Nat) (s₀ : State)

abbrev key : Addr := s₀.gpr .rdi
abbrev up : Addr := s₀.gpr .rsi
abbrev tp : Addr := s₀.gpr .rcx
abbrev scr : Addr := s₀.gpr .r8
/-- The number of steps. -/
abbrev nn : Nat := ((s₀.gpr .rdx).setWidth 32).toNat
abbrev keyR : Region := ⟨VG.Proof.Pbkdf2.X86_64.key s₀, 2 * (P.N + P.B)⟩
abbrev uR : Region := ⟨VG.Proof.Pbkdf2.X86_64.up s₀, D⟩
abbrev tR : Region := ⟨VG.Proof.Pbkdf2.X86_64.tp s₀, D⟩
abbrev scR : Region := ⟨VG.Proof.Pbkdf2.X86_64.scr s₀, 8 * W⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 8
/-- The hash value being compressed, and the block. -/
abbrev hv : Addr := VG.Proof.Pbkdf2.X86_64.scr s₀ + BitVec.ofNat 64 (P.so + 48)
abbrev blk : Addr := VG.Proof.Pbkdf2.X86_64.scr s₀ + BitVec.ofNat 64 (P.so + 48 + P.N)

end

structure Pre (P : Params) (D W : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Pbkdf2.X86_64.keyR P s₀, VG.Proof.Pbkdf2.X86_64.uR D s₀]
  wr : s₀.wr = [VG.Proof.Pbkdf2.X86_64.tR D s₀, VG.Proof.Pbkdf2.X86_64.scR W s₀]
  k_t : (VG.Proof.Pbkdf2.X86_64.keyR P s₀).Disjoint (VG.Proof.Pbkdf2.X86_64.tR D s₀)
  k_s : (VG.Proof.Pbkdf2.X86_64.keyR P s₀).Disjoint (VG.Proof.Pbkdf2.X86_64.scR W s₀)
  u_t : (VG.Proof.Pbkdf2.X86_64.uR D s₀).Disjoint (VG.Proof.Pbkdf2.X86_64.tR D s₀)
  u_s : (VG.Proof.Pbkdf2.X86_64.uR D s₀).Disjoint (VG.Proof.Pbkdf2.X86_64.scR W s₀)
  t_s : (VG.Proof.Pbkdf2.X86_64.tR D s₀).Disjoint (VG.Proof.Pbkdf2.X86_64.scR W s₀)
  ret_k : (VG.Proof.Pbkdf2.X86_64.retR s₀).Disjoint (VG.Proof.Pbkdf2.X86_64.keyR P s₀)
  ret_u : (VG.Proof.Pbkdf2.X86_64.retR s₀).Disjoint (VG.Proof.Pbkdf2.X86_64.uR D s₀)
  ret_t : (VG.Proof.Pbkdf2.X86_64.retR s₀).Disjoint (VG.Proof.Pbkdf2.X86_64.tR D s₀)
  ret_s : (VG.Proof.Pbkdf2.X86_64.retR s₀).Disjoint (VG.Proof.Pbkdf2.X86_64.scR W s₀)
  stk_k : (VG.Proof.Pbkdf2.X86_64.stkR s₀).Disjoint (VG.Proof.Pbkdf2.X86_64.keyR P s₀)
  stk_u : (VG.Proof.Pbkdf2.X86_64.stkR s₀).Disjoint (VG.Proof.Pbkdf2.X86_64.uR D s₀)
  stk_t : (VG.Proof.Pbkdf2.X86_64.stkR s₀).Disjoint (VG.Proof.Pbkdf2.X86_64.tR D s₀)
  stk_s : (VG.Proof.Pbkdf2.X86_64.stkR s₀).Disjoint (VG.Proof.Pbkdf2.X86_64.scR W s₀)

theorem pre_of {P : Params} {D W : Nat} {S : StreamingHash} (hS : S.stateBytes = P.N + P.B)
    (hD : S.digestBytes = D) {s₀ : State} (h : (VG.Proof.Pbkdf2.X86_64.iterK S W).pre s₀) : VG.Proof.Pbkdf2.X86_64.Pre P D W s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, -⟩ := h
  simp only [hS, hD] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- The return address and the 8 bytes below it. -/
theorem ret_stk (s₀ : State) : (VG.Proof.Pbkdf2.X86_64.retR s₀).Disjoint (VG.Proof.Pbkdf2.X86_64.stkR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

/-! ## The parts of the scratch space -/

section
variable {P : Params} {D W : Nat} (hz : VG.Proof.Pbkdf2.X86_64.Sizes P D W) {s₀ : State} (hp : VG.Proof.Pbkdf2.X86_64.Pre P D W s₀)
include hz

theorem so_le : P.so ≤ 2048 := hz.dims.so
theorem N_le : P.N ≤ 64 := hz.dims.N.2
theorem B_le : P.B ≤ 128 := by rcases hz.dims.B with h | h <;> omega
theorem B_ge : 64 ≤ P.B := by rcases hz.dims.B with h | h <;> omega

omit hz in
theorem scr_sub (s₀ : State) {a n : Nat} (h : a + n ≤ 8 * W) :
    Region.Sub ⟨VG.Proof.Pbkdf2.X86_64.scr s₀ + BitVec.ofNat 64 a, n⟩ (VG.Proof.Pbkdf2.X86_64.scR W s₀) :=
  Offset.sub_base _ h

end

/-! ## The registers during a step -/

/-- What holds between the pieces of a step: the regions, our registers, and
memory outside the scratch space, `T` and the stack as on entry. -/
structure Regs (P : Params) (D W : Nat) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rbx : s.gpr .rbx = VG.Proof.Pbkdf2.X86_64.hv P s₀
  rbp : s.gpr .rbp = VG.Proof.Pbkdf2.X86_64.blk P s₀
  r12 : s.gpr .r12 = VG.Proof.Pbkdf2.X86_64.key s₀
  r13 : s.gpr .r13 = VG.Proof.Pbkdf2.X86_64.tp s₀
  r15 : s.gpr .r15 = VG.Proof.Pbkdf2.X86_64.scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  frame : Frame [VG.Proof.Pbkdf2.X86_64.tR D s₀, VG.Proof.Pbkdf2.X86_64.scR W s₀, VG.Proof.Pbkdf2.X86_64.stkR s₀] s₀.mem s.mem

section
variable {P : Params} {D W : Nat} (hz : VG.Proof.Pbkdf2.X86_64.Sizes P D W) {s₀ : State} (hp : VG.Proof.Pbkdf2.X86_64.Pre P D W s₀)

/-- `Regs` after code that keeps our registers and writes only memory in the
regions it allows. -/
theorem Regs.write {s s' : State} (h : VG.Proof.Pbkdf2.X86_64.Regs P D W s₀ s)
    (hg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → r ≠ .r14 → s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hm : Frame [VG.Proof.Pbkdf2.X86_64.tR D s₀, VG.Proof.Pbkdf2.X86_64.scR W s₀, VG.Proof.Pbkdf2.X86_64.stkR s₀] s.mem s'.mem) :
    VG.Proof.Pbkdf2.X86_64.Regs P D W s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := (hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.rbx
  rbp := (hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.rbp
  r12 := (hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.r12
  r13 := (hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.r13
  r15 := (hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.r15
  rsp := (hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.rsp
  frame := h.frame.trans hm

omit hp in
/-- A part of the scratch space, as a frame of `Regs`. -/
theorem frame_scr {m m' : Mem} {a n : Nat} (h : a + n ≤ 8 * W)
    (hf : Frame [⟨VG.Proof.Pbkdf2.X86_64.scr s₀ + BitVec.ofNat 64 a, n⟩] m m') : Frame [VG.Proof.Pbkdf2.X86_64.tR D s₀, VG.Proof.Pbkdf2.X86_64.scR W s₀, VG.Proof.Pbkdf2.X86_64.stkR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.Pbkdf2.X86_64.scR W s₀, by simp, VG.Proof.Pbkdf2.X86_64.scr_sub s₀ h⟩

include hz hp

/-- The hash value at `key + o` into the scratch space. -/
theorem load_ok {H : Md P.B P.N P.L} (hR : H.Reloc) {s : State} (h : VG.Proof.Pbkdf2.X86_64.Regs P D W s₀ s) {o : Nat}
    (ho : o + P.N ≤ 2 * (P.N + P.B)) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      Frame [⟨VG.Proof.Pbkdf2.X86_64.hv P s₀, P.N⟩] s.mem s'.mem →
      H.stateAt s'.mem (VG.Proof.Pbkdf2.X86_64.hv P s₀) = H.stateAt s₀.mem (VG.Proof.Pbkdf2.X86_64.key s₀ + BitVec.ofNat 64 o) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (loadKey P o ++ rest)) s Q := by
  have := VG.Proof.Pbkdf2.X86_64.so_le hz; have := VG.Proof.Pbkdf2.X86_64.N_le hz; have := VG.Proof.Pbkdf2.X86_64.B_le hz; have hz_N4 := hz.N4; have hz_fits := hz.fits
  have hn : 4 * (P.N / 4) = P.N := by omega
  unfold loadKey
  refine VG.Proof.Pbkdf2.X86_64.copy32_ok (by decide) (by decide) o 0 (P.N / 4) rest s Q (fun j hj => ?_) (fun j hj => ?_) ?_
    (by omega) fun s' g' rd' wr' m' => ?_
  · rw [h.r12, h.rd, hp.rd, add_ofNat]
    exact ⟨VG.Proof.Pbkdf2.X86_64.keyR P s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [h.rbx, h.wr, hp.wr, add_ofNat, add_ofNat]
    exact ⟨VG.Proof.Pbkdf2.X86_64.scR W s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [h.r12, h.rbx, hn, add_ofNat, Nat.add_zero]
    exact hp.k_s.sep (Offset.contains_base _ (by omega) (by omega))
      (Offset.contains_base _ (by omega_using [hz_fits]) (by omega))
  rw [h.rbx, h.r12, hn, add_ofNat, Nat.add_zero] at m'
  refine k s' g' rd' wr' (by rw [m']; exact VG.WriteBytes.writeBytes_frame _ _ _ (by
    rw [bytesAt_length]; exact Region.contains_self _ _)) ?_
  refine hR _ _ _ _ fun i hi => ?_
  rw [m', writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
    bytesAt_getD' _ _ hi, add_ofNat]
  exact h.frame.bytes (R := VG.Proof.Pbkdf2.X86_64.keyR P s₀) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.k_t
    · exact hp.k_s
    · exact hp.stk_k.symm) (by show 2 * (P.N + P.B) ≤ 2 ^ 64; omega) (by show o + i < 2 * (P.N + P.B); omega_using [hi, ho])

/-- What the call of the compression function needs, with the block's address in `rsi`. -/
theorem callOk_of {s : State} (h : VG.Proof.Pbkdf2.X86_64.Regs P D W s₀ s) (hsi : s.gpr .rsi = VG.Proof.Pbkdf2.X86_64.blk P s₀) :
    CallOk P s (VG.Proof.Pbkdf2.X86_64.hv P s₀) (VG.Proof.Pbkdf2.X86_64.scr s₀) (VG.Proof.Pbkdf2.X86_64.blk P s₀) := by
  have := VG.Proof.Pbkdf2.X86_64.so_le hz; have := VG.Proof.Pbkdf2.X86_64.N_le hz; have := VG.Proof.Pbkdf2.X86_64.B_le hz; have hz_fits := hz.fits
  have hsc : VG.Proof.Pbkdf2.X86_64.scR W s₀ ∈ s.wr := by simp [h.wr, hp.wr]
  have stk : ∀ {a n : Nat}, a + n ≤ 8 * W →
      (below (s.gpr .rsp) 8).Disjoint ⟨VG.Proof.Pbkdf2.X86_64.scr s₀ + BitVec.ofNat 64 a, n⟩ :=
    fun h' => by rw [h.rsp]; exact hp.stk_s.sub_right (VG.Proof.Pbkdf2.X86_64.scr_sub s₀ h')
  refine ⟨h.rbx, h.r15, hsi, Offset.disjoint_base _ (by omega) (by omega),
    Offset.disjoint _ (by omega) (by omega) (by omega), Offset.disjoint_base _ (by omega) (by omega),
    stk (by omega), by simpa using stk (a := 0) (n := P.so) (by omega), stk (by omega), ?_, ?_⟩
  · refine Covers.of_sub fun r hr => ⟨VG.Proof.Pbkdf2.X86_64.scR W s₀, List.mem_append_right _ hsc, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, rfl, by dsimp only; omega⟩
    · exact ⟨_, rfl, by dsimp only; omega⟩
    · exact ⟨0, by simp, by dsimp only; omega⟩
  · refine Covers.of_sub fun r hr => ⟨VG.Proof.Pbkdf2.X86_64.scR W s₀, hsc, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, rfl, by dsimp only; omega⟩
    · exact ⟨0, by simp, by dsimp only; omega⟩

/-- A call of the compression function on the block. -/
theorem cmp_ok {H : Md P.B P.N P.L} {name : String} {code : Prog isa} (hf : CalleeOk H code) {s : State}
    (h : VG.Proof.Pbkdf2.X86_64.Regs P D W s₀ s) {Q : State → Prop}
    (k : ∀ s', VG.Proof.Pbkdf2.X86_64.Regs P D W s₀ s' → s'.gpr .r14 = s.gpr .r14 →
      Frame [⟨VG.Proof.Pbkdf2.X86_64.hv P s₀, P.N⟩, ⟨VG.Proof.Pbkdf2.X86_64.scr s₀, P.so⟩, VG.Proof.Pbkdf2.X86_64.stkR s₀] s.mem s'.mem →
      H.stateAt s'.mem (VG.Proof.Pbkdf2.X86_64.hv P s₀) = H.compress (H.stateAt s.mem (VG.Proof.Pbkdf2.X86_64.hv P s₀)) (H.blockAt s.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀)) →
      Q s') :
    WP isa (compressBlock name code) s Q := by
  have := VG.Proof.Pbkdf2.X86_64.so_le hz; have := VG.Proof.Pbkdf2.X86_64.N_le hz; have := VG.Proof.Pbkdf2.X86_64.B_le hz; have hz_fits := hz.fits
  unfold compressBlock
  refine WP.seq (wp_mov fun s₁ u₁ _ _ => WP.block_nil ?_)
  have hsp : s₁.gpr .rsp = s₀.gpr .rsp := by rw [u₁.other _ (by decide), h.rsp]
  have h₁ := h.write (fun r _ _ _ hr _ _ => u₁.other r hr) u₁.rd u₁.wr (by rw [u₁.mem]; exact Frame.refl _ _)
  refine compressAt_ok H hf (VG.Proof.Pbkdf2.X86_64.callOk_of hz hp h₁ (by rw [u₁.gpr, h.rbp])) (by omega) (by omega)
    fun s' hrd hwr hcs hfr hst _ _ => ?_
  have cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r := fun r hr => by
    rw [hcs r hr, u₁.other r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  rw [hsp, u₁.mem] at hfr
  rw [u₁.mem] at hst
  refine k s' ⟨hrd.trans (u₁.rd.trans h.rd), hwr.trans (u₁.wr.trans h.wr),
    (cs _ (by simp [calleeSaved])).trans h.rbx, (cs _ (by simp [calleeSaved])).trans h.rbp,
    (cs _ (by simp [calleeSaved])).trans h.r12, (cs _ (by simp [calleeSaved])).trans h.r13,
    (cs _ (by simp [calleeSaved])).trans h.r15, (cs _ (by simp [calleeSaved])).trans h.rsp,
    h.frame.trans (hfr.sub fun r hr => ?_)⟩ (cs _ (by simp [calleeSaved])) hfr hst
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨VG.Proof.Pbkdf2.X86_64.scR W s₀, by simp, VG.Proof.Pbkdf2.X86_64.scr_sub s₀ (by omega)⟩
  · exact ⟨VG.Proof.Pbkdf2.X86_64.scR W s₀, by simp, Region.sub_prefix (by omega)⟩
  · exact ⟨VG.Proof.Pbkdf2.X86_64.stkR s₀, by simp, fun _ h => h⟩

end

/-! ## Words of the block and of `T` -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_xor32m {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' d ((((s.gpr d).setWidth 32) ^^^ s.mem.readW a 32).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu32 .xor d (.mem m) :: is)) s Q := by
  refine MdStream.X86_64.WP.cons
    (s' := (arithFlags s (((s.gpr d).setWidth 32) ^^^ s.mem.readW a 32) false false).setReg d _) ?_
    (k _ (Upd.flags _ _ _ _ _ _))
  simp [exec, execAlu32, readSrc32, State.load32, State.setReg32, ha, hin]

theorem wp_mov32r {d r : Reg} (k : ∀ s', Upd s s' d (((s.gpr r).setWidth 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.reg r) :: is)) s Q :=
  MdStream.X86_64.WP.cons rfl (k _ (Upd.setReg _ _ _))

end

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
theorem xor_ok {tp bp : Addr} {D : Nat} (hd : Region.Disjoint ⟨tp, D⟩ ⟨bp, D⟩) (hD : D < 2 ^ 32) :
    ∀ n, 4 * n ≤ D → ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .rbp = bp → s.gpr .r13 = tp →
    (∀ k < n, InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (tp + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = VG.WriteBytes.writeBytes s.mem tp
        (Spec.Pbkdf2.xorBytes (bytesAt s.mem tp (4 * n)) (bytesAt s.mem bp (4 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap xorW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [bytesAt, Spec.Pbkdf2.xorBytes, VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q hbp h13 hin hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q hbp h13 (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [xorW, List.cons_append, List.nil_append]
    refine wp_mov32m (a := bp + BitVec.ofNat 64 (4 * n))
      (by rw [ea_at, g₁ _ (by decide), hbp, ofInt_natCast]) (by rw [rd₁, wr₁]; exact hin n (by omega))
      fun s₂ u₂ => ?_
    have hw := hout n (by omega)
    refine VG.Proof.Pbkdf2.X86_64.wp_xor32m (a := tp + BitVec.ofNat 64 (4 * n))
      (by rw [ea_at, u₂.other _ (by decide), g₁ _ (by decide), h13, ofInt_natCast])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; obtain ⟨r, hr, hc⟩ := hw; exact ⟨r, List.mem_append_right _ hr, hc⟩)
      fun s₃ u₃ => ?_
    refine wp_store32 (a := tp + BitVec.ofNat 64 (4 * n))
      (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), h13, ofInt_natCast])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hw)
      fun s₄ g₄ m₄ rd₄ wr₄ => k s₄ (fun r hr => by rw [g₄, u₃.other r hr, u₂.other r hr, g₁ r hr])
        (by rw [rd₄, u₃.rd, u₂.rd, rd₁]) (by rw [wr₄, u₃.wr, u₂.wr, wr₁]) ?_
    have hl : (Spec.Pbkdf2.xorBytes (bytesAt s.mem tp (4 * n)) (bytesAt s.mem bp (4 * n))).length = 4 * n := by
      rw [Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    rw [m₄, u₃.gpr, u₃.mem, u₂.gpr, u₂.mem, setWidth32, setWidth32, VG.Proof.Pbkdf2.X86_64.writeW_xor32, m₁,
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

/-- Stores of zero (the low 32 bits of `rax`) at `rbp + a + 4 + 4 k`, for `k < n`. -/
theorem zeros_ok {a : Nat} {p : Addr} : ∀ n (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr .rbp = p → (s.gpr .rax).setWidth 32 = 0 →
    (∀ k < n, InRegions s.wr (p + BitVec.ofNat 64 (a + 4 + 4 * k)) 4) → 4 * n < 2 ^ 64 →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = VG.WriteBytes.writeBytes s.mem (p + BitVec.ofNat 64 (a + 4)) (List.replicate (4 * n) 0) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).map (fun k => Instr.store32 (at_ .rbp (a + 4 + 4 * k)) .rax) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s rfl rfl rfl (by simp [VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro rest s Q hbp hax hout hn k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih _ s Q hbp hax (fun j hj => hout j (by omega)) (by omega) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_store32 (a := p + BitVec.ofNat 64 (a + 4 + 4 * n)) (by rw [ea_at, g₁, hbp, ofInt_natCast])
      (by rw [wr₁]; exact hout n (by omega)) fun s₂ g₂ m₂ rd₂ wr₂ =>
        k s₂ (by rw [g₂, g₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) ?_
    rw [m₂, g₁, hax, m₁, Memory.writeW_bytes _ _ (0 : BitVec 32) [0, 0, 0, 0] (by decide),
      Memory.writeBytes_append' _ _ _ (by rw [List.length_replicate, add_ofNat]) (by simp; omega), Nat.mul_succ,
      ← List.replicate_append_replicate]
    rfl

/-- `padFrom a b` writes `0x80` and zeros from byte `a` to byte `b` of the block at `rbp`. -/
theorem padFrom_ok {a b : Nat} (hab : a + 4 ≤ b) (h4 : (b - a) % 4 = 0) (hb : b < 2 ^ 31) {s : State} {p : Addr}
    (hbp : s.gpr .rbp = p) (hout : ∀ k < (b - a) / 4, InRegions s.wr (p + BitVec.ofNat 64 (a + 4 * k)) 4)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = VG.WriteBytes.writeBytes s.mem (p + BitVec.ofNat 64 a) ([0x80] ++ List.replicate (b - a - 1) 0) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (padFrom a b ++ rest)) s Q := by
  unfold padFrom
  simp only [List.cons_append, List.nil_append]
  refine wp_mov32i fun s₁ u₁ _ _ => ?_
  refine wp_store32 (a := p + BitVec.ofNat 64 a) (by rw [ea_at, u₁.other _ (by decide), hbp, ofInt_natCast])
    (by rw [u₁.wr]; simpa using hout 0 (by omega)) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_mov32i fun s₃ u₃ _ _ => ?_
  refine VG.Proof.Pbkdf2.X86_64.zeros_ok (a := a) ((b - a) / 4 - 1) rest s₃ Q (by rw [u₃.other _ (by decide), g₂, u₁.other _ (by decide),
                           hbp]) (by rw [u₃.gpr, setWidth32]) (fun j hj => by
      rw [u₃.wr, wr₂, u₁.wr, show a + 4 + 4 * j = a + 4 * (j + 1) by omega]; exact hout (j + 1) (by omega))
    (by omega) fun s₄ g₄ rd₄ wr₄ m₄ => k s₄ (fun r hr => by
      rw [g₄, u₃.other r hr, g₂, u₁.other r hr]) (by rw [rd₄, u₃.rd, rd₂, u₁.rd]) (by rw [wr₄, u₃.wr, wr₂, u₁.wr]) ?_
  rw [m₄, u₃.mem, m₂, u₁.gpr, u₁.mem, setWidth32,
    Memory.writeW_bytes _ _ (0x80 : BitVec 32) [0x80, 0, 0, 0] (by decide),
    Memory.writeBytes_append' _ _ _ (by rw [List.length_cons, List.length_cons, List.length_cons,
      List.length_singleton, add_ofNat]) (by simp; omega),
    show b - a - 1 = 3 + 4 * ((b - a) / 4 - 1) by omega, ← List.replicate_append_replicate]
  rfl

/-- `padLen` writes the rest of the block at `p` (`rbp`) after its first `D`
bytes, which it keeps: the padding of a `B + D`-byte message, whose length
field `P.len` stores at `rbx + N + B - L`, the block's end. -/
theorem padLen_ok {P : Params} {D : Nat} {H : Md P.B P.N P.L} (hs : Shape H) (hok : H.lenOk (P.B + D))
    (hD4 : D % 4 = 0) (hL4 : P.L % 4 = 0) (hB4 : P.B % 4 = 0) (hpad : D + 4 ≤ P.B - P.L) (hB : P.B ≤ 128)
    {s : State} {p : Addr} (hbp : s.gpr .rbp = p)
    (hbx : s.gpr .rbx + BitVec.ofNat 64 (P.N + P.B - P.L) = p + BitVec.ofNat 64 (P.B - P.L))
    (hw : ∀ a n, a + n ≤ P.B → InRegions s.wr (p + BitVec.ofNat 64 a) n) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .rax → r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      Frame [⟨p, P.B⟩] s.mem s'.mem → bytesAt s'.mem (p + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D →
      bytesAt s'.mem p D = bytesAt s.mem p D → WP isa (.block rest) s' Q) :
    WP isa (.block (Impl.Pbkdf2.X86_64.padLen P D ++ rest)) s Q := by
  unfold Impl.Pbkdf2.X86_64.padLen
  simp only [List.append_assoc]
  refine VG.Proof.Pbkdf2.X86_64.padFrom_ok (a := D) (b := P.B - P.L) (by omega) (by omega) (by omega_using [hB]) hbp
    (fun j hj => hw _ _ (by omega_using [hj])) fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  refine wp_mov32i fun s₃ u₃ _ _ => ?_
  change WP isa (.block (P.len ++ rest)) s₃ Q
  rw [WP.block_append_iff]
  refine WP.mono (hs.len s₃ ?_) fun s₄ ⟨g₄, rd₄, wr₄, m₄⟩ => ?_
  · rw [u₃.other _ (by decide), g₂ _ (by decide), hbx, u₃.wr, wr₂]; exact hw _ _ (by omega_using [hpad])
  rw [u₃.other _ (by decide), g₂ _ (by decide), hbx, u₃.gpr, zx_ofNat (by omega_using [hB, hpad]), H.lenOf_eq _ hok, u₃.mem,
    m₂] at m₄
  have lpz : ([0x80] ++ List.replicate (P.B - P.L - D - 1) 0 : List Byte).length = P.B - P.L - D := by simp; omega_using [hpad]
  have S1 : Mem.Sep p D (p + BitVec.ofNat 64 D) (P.B - P.L - D) := by
    have := Offset.sep p (d := 0) (n := D) (e := D) (k := P.B - P.L - D) (.inl (by omega)) (by omega_using [hB, hpad]) (by omega_using [hB, hpad])
    rwa [BitVec.add_zero] at this
  have S2 : ∀ {a n : Nat}, a + n ≤ P.B - P.L →
      Mem.Sep (p + BitVec.ofNat 64 a) n (p + BitVec.ofNat 64 (P.B - P.L)) P.L :=
    fun h' => Offset.sep _ (.inl h') (by omega_using [h', hB]) (by omega_using [hB, hpad])
  refine k s₄ (fun r h1 h2 => by rw [g₄ r h1, u₃.other r h2, g₂ r h1]) (by rw [rd₄, u₃.rd, rd₂])
    (by rw [wr₄, u₃.wr, wr₂]) ?_ ?_ ?_
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
        rw [H.lenBytes_length]; have := S2 (a := 0) (n := D) (by omega_using [hpad]); rwa [BitVec.add_zero] at this) (by omega),
      bytesAt_writeBytes_sep _ _ (by rw [lpz]; exact S1) (by omega)]

/-! ## The digest into the block -/

theorem blk_sep (P : Params) (s₀ : State) {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a + n ≤ 2 ^ 32)
    (hb : b + k ≤ 2 ^ 32) (hN : P.so + 48 + P.N ≤ 2 ^ 32) :
    Mem.Sep (VG.Proof.Pbkdf2.X86_64.blk P s₀ + BitVec.ofNat 64 a) n (VG.Proof.Pbkdf2.X86_64.blk P s₀ + BitVec.ofNat 64 b) k := by
  rw [add_ofNat, add_ofNat]
  exact Offset.sep _ (by omega) (by omega) (by omega)

theorem blk0 (P : Params) (s₀ : State) : VG.Proof.Pbkdf2.X86_64.blk P s₀ + BitVec.ofNat 64 0 = VG.Proof.Pbkdf2.X86_64.blk P s₀ := by simp

section
variable {P : Params} {D W : Nat} (hz : VG.Proof.Pbkdf2.X86_64.Sizes P D W) {s₀ : State} (hp : VG.Proof.Pbkdf2.X86_64.Pre P D W s₀)
include hz hp

theorem in_scr {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ 8 * W) :
    InRegions s.wr (VG.Proof.Pbkdf2.X86_64.scr s₀ + BitVec.ofNat 64 a) n :=
  ⟨VG.Proof.Pbkdf2.X86_64.scR W s₀, by simp [hwr, hp.wr], Offset.contains_base _ h (by have hz_W := hz.W; omega)⟩

theorem in_blk {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ P.B) :
    InRegions s.wr (VG.Proof.Pbkdf2.X86_64.blk P s₀ + BitVec.ofNat 64 a) n := by
  have hz_fits := hz.fits
  rw [add_ofNat]; exact VG.Proof.Pbkdf2.X86_64.in_scr hz hp hwr (by omega)

/-- The digest of the hash value into the block's first `D` bytes, the padding after them as it was. -/
theorem digest_ok {H : Md P.B P.N P.L} (hs : Shape H) {s : State} (h : VG.Proof.Pbkdf2.X86_64.Regs P D W s₀ s)
    (hpad : bytesAt s.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      Frame [⟨VG.Proof.Pbkdf2.X86_64.blk P s₀, P.N⟩] s.mem s'.mem →
      bytesAt s'.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀) D = (H.digest (H.stateAt s.mem (VG.Proof.Pbkdf2.X86_64.hv P s₀))).take D →
      bytesAt s'.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D → WP isa (.block rest) s' Q) :
    WP isa (.block (Impl.Pbkdf2.X86_64.digest P D ++ rest)) s Q := by
  have := VG.Proof.Pbkdf2.X86_64.so_le hz; have := VG.Proof.Pbkdf2.X86_64.N_le hz; have := VG.Proof.Pbkdf2.X86_64.B_le hz; have hz_fits := hz.fits; have hz_DN := hz.DN; have hz_NL := hz.NL
  have hz_D4 := hz.D4; have hz_N4 := hz.N4; have hz_pad := hz.pad
  unfold Impl.Pbkdf2.X86_64.digest
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (hs.out s ?_ ?_ ?_) fun s₁ ⟨g₁, rd₁, wr₁, m₁⟩ => ?_
  · rw [h.rbx]
    obtain ⟨r, hr, hc⟩ := VG.Proof.Pbkdf2.X86_64.in_scr hz hp h.wr (a := P.so + 48) (n := P.N) (by omega_using [hz_fits])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · rw [h.rbp]; exact VG.Proof.Pbkdf2.X86_64.in_scr hz hp h.wr (by omega_using [hz_NL, hz_fits])
  · rw [h.rbx, h.rbp]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  rw [h.rbp, h.rbx] at m₁
  have hdl := H.digest_length (H.stateAt s.mem (VG.Proof.Pbkdf2.X86_64.hv P s₀))
  have f₁ : Frame [⟨VG.Proof.Pbkdf2.X86_64.blk P s₀, P.N⟩] s.mem s₁.mem := by
    rw [m₁]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hdl]; exact Region.contains_self _ _)
  have b₁ : bytesAt s₁.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀) D = (H.digest (H.stateAt s.mem (VG.Proof.Pbkdf2.X86_64.hv P s₀))).take D := by
    rw [bytesAt_take _ _ (Nat.le_of_lt_succ (Nat.lt_succ_of_le hz.DN)), m₁, bytesAt_writeBytes_self' hdl (by omega_using [hz_NL, this])]
  have r₁ : bytesAt s₁.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀ + BitVec.ofNat 64 P.N) (P.B - P.N) =
      bytesAt s.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀ + BitVec.ofNat 64 P.N) (P.B - P.N) := by
    rw [m₁]
    refine bytesAt_writeBytes_sep _ _ ?_ (by omega_using [this])
    have := VG.Proof.Pbkdf2.X86_64.blk_sep P s₀ (a := P.N) (n := P.B - P.N) (b := 0) (k := P.N) (.inr (by omega)) (by omega_using [hz_NL, this]) (by omega_using [hz_NL, this])
      (by omega)
    rw [VG.Proof.Pbkdf2.X86_64.blk0] at this; rw [hdl]; exact this
  have hsplit : ∀ m : Mem, bytesAt m (VG.Proof.Pbkdf2.X86_64.blk P s₀ + BitVec.ofNat 64 D) (P.B - D) =
      bytesAt m (VG.Proof.Pbkdf2.X86_64.blk P s₀ + BitVec.ofNat 64 D) (P.N - D) ++ bytesAt m (VG.Proof.Pbkdf2.X86_64.blk P s₀ + BitVec.ofNat 64 P.N) (P.B - P.N) := by
    intro m
    rw [show P.B - D = (P.N - D) + (P.B - P.N) by omega_using [hz_NL, hz_DN], bytesAt_add, add_ofNat (VG.Proof.Pbkdf2.X86_64.blk P s₀),
      show D + (P.N - D) = P.N by omega_using [hz_DN]]
  have hY : bytesAt s.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀ + BitVec.ofNat 64 P.N) (P.B - P.N) = (H.tailPad D).drop (P.N - D) := by
    rw [← hpad, hsplit, List.drop_left' (bytesAt_length _ _ _)]
  by_cases hDN : D < P.N
  · simp only [hDN, ↓reduceIte]
    refine VG.Proof.Pbkdf2.X86_64.padFrom_ok (a := D) (b := P.N) (by omega) (by omega_using [hz_N4, hz_D4]) (by omega_using [hz_NL, this]) (s := s₁) (p := VG.Proof.Pbkdf2.X86_64.blk P s₀)
      (by rw [g₁ _ (by decide), h.rbp]) (fun j hj => VG.Proof.Pbkdf2.X86_64.in_blk hz hp (wr₁.trans h.wr) (by omega_using [hj, hz_NL]))
      fun s₂ g₂ rd₂ wr₂ m₂ => k s₂ (fun r hr => (g₂ r hr).trans (g₁ r hr)) (rd₂.trans rd₁) (wr₂.trans wr₁) ?_ ?_ ?_
    · rw [m₂]
      refine f₁.trans (VG.WriteBytes.writeBytes_frame _ _ _ ?_)
      simp only [List.length_append, List.length_singleton, List.length_replicate]
      exact Offset.contains_base _ (by omega_using [hDN]) (by omega_using [hz_NL, hz_DN, this])
    · rw [m₂, bytesAt_writeBytes_sep _ _ ?_ (by omega), b₁]
      have := VG.Proof.Pbkdf2.X86_64.blk_sep P s₀ (a := 0) (n := D) (b := D) (k := P.N - D) (.inl (by omega)) (by omega_using [hz_NL, hz_DN, this]) (by omega_using [hz_NL, hz_DN, this])
        (by omega)
      rw [VG.Proof.Pbkdf2.X86_64.blk0] at this
      have e : ([0x80] ++ List.replicate (P.N - D - 1) 0 : List Byte).length = P.N - D := by simp; omega_using [hDN]
      rw [e]; exact this
    · have hfix : [(0x80 : Byte)] ++ List.replicate (P.N - D - 1) 0 = (H.tailPad D).take (P.N - D) :=
        (H.tailPad_take (by omega_using [hDN]) (by omega_using [hz_NL, hz_DN])).symm
      have hfl : ((H.tailPad D).take (P.N - D)).length = P.N - D := by
        rw [List.length_take, H.tailPad_length (by omega_using [hz_pad])]; omega_using [hz_NL]
      rw [hsplit, m₂, hfix, bytesAt_writeBytes_self' hfl (by omega_using [hz_NL, this]),
        bytesAt_writeBytes_sep _ _ ?_ (by omega), r₁, hY, List.take_append_drop]
      have := VG.Proof.Pbkdf2.X86_64.blk_sep P s₀ (a := P.N) (n := P.B - P.N) (b := D) (k := P.N - D) (.inr (by omega_using [hz_DN])) (by omega)
        (by omega) (by omega)
      rw [hfl]; exact this
  · simp only [hDN, ↓reduceIte, List.nil_append]
    obtain rfl : D = P.N := by omega_using [hDN, hz_DN]
    refine k s₁ g₁ rd₁ wr₁ f₁ b₁ ?_
    rw [r₁, hY, Nat.sub_self, List.drop_zero]

end

/-! ## A step -/

section
variable (P : Params) (D : Nat) (H : Md P.B P.N P.L) (s₀ : State)

/-- A step, as the code computes it, from the key's inner and outer hash values. -/
abbrev stepM : List Byte → List Byte :=
  H.step D (H.stateAt s₀.mem (VG.Proof.Pbkdf2.X86_64.key s₀)) (H.stateAt s₀.mem (VG.Proof.Pbkdf2.X86_64.key s₀ + BitVec.ofNat 64 (P.N + P.B)))

/-- What the body writes: the compression function's scratch space, the hash
value and the block, `T` and the stack. -/
abbrev bodyR : List Region := [⟨VG.Proof.Pbkdf2.X86_64.scr s₀, P.so⟩, ⟨VG.Proof.Pbkdf2.X86_64.hv P s₀, P.N + P.B⟩, VG.Proof.Pbkdf2.X86_64.tR D s₀, VG.Proof.Pbkdf2.X86_64.stkR s₀]

end

/-- The loop invariant, with `r` steps left. -/
structure Inv (P : Params) (D W : Nat) (H : Md P.B P.N P.L) (s₀ : State) (r : Nat) (s : State) : Prop
    extends VG.Proof.Pbkdf2.X86_64.Regs P D W s₀ s where
  r14 : s.gpr .r14 = BitVec.ofNat 64 r
  saved : Saved P s₀ .r8 s.mem
  pad : bytesAt s.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D
  le : r ≤ VG.Proof.Pbkdf2.X86_64.nn s₀
  val : Spec.Pbkdf2.iterate (VG.Proof.Pbkdf2.X86_64.stepM P D H s₀) (VG.Proof.Pbkdf2.X86_64.nn s₀) (bytesAt s₀.mem (VG.Proof.Pbkdf2.X86_64.up s₀) D) (bytesAt s₀.mem (VG.Proof.Pbkdf2.X86_64.tp s₀) D) =
    Spec.Pbkdf2.iterate (VG.Proof.Pbkdf2.X86_64.stepM P D H s₀) r (bytesAt s.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀) D) (bytesAt s.mem (VG.Proof.Pbkdf2.X86_64.tp s₀) D)

section
variable {P : Params} {D W : Nat} (hz : VG.Proof.Pbkdf2.X86_64.Sizes P D W) {s₀ : State} (hp : VG.Proof.Pbkdf2.X86_64.Pre P D W s₀)
include hz hp

/-- The saved registers are outside what the body writes. -/
theorem saved_frame {m m' : Mem} (h : Saved P s₀ .r8 m) (hf : Frame (VG.Proof.Pbkdf2.X86_64.bodyR P D s₀) m m') : Saved P s₀ .r8 m' := by
  have := VG.Proof.Pbkdf2.X86_64.so_le hz; have := VG.Proof.Pbkdf2.X86_64.N_le hz; have := VG.Proof.Pbkdf2.X86_64.B_le hz; have hz_fits := hz.fits
  intro q hq
  rw [← h q hq]
  have hd := saved_offset hz.dims hq
  rw [ofInt_natCast]
  refine hf.readW (r := ⟨VG.Proof.Pbkdf2.X86_64.scr s₀ + BitVec.ofNat 64 q.2, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  · exact (hp.t_s.sub_right (VG.Proof.Pbkdf2.X86_64.scr_sub s₀ (by omega))).symm
  · exact (hp.stk_s.sub_right (VG.Proof.Pbkdf2.X86_64.scr_sub s₀ (by omega))).symm

omit hz hp in
/-- A range of the scratch space from `hv` on, within what the body writes. -/
theorem sub_body {a n : Nat} (h₁ : P.so + 48 ≤ a) (h₂ : a + n ≤ P.so + 48 + P.N + P.B) :
    ∃ r' ∈ VG.Proof.Pbkdf2.X86_64.bodyR P D s₀, Region.Sub ⟨VG.Proof.Pbkdf2.X86_64.scr s₀ + BitVec.ofNat 64 a, n⟩ r' :=
  ⟨⟨VG.Proof.Pbkdf2.X86_64.hv P s₀, P.N + P.B⟩, by simp, Offset.sub _ h₁ (by omega)⟩

/-- A range of the block disjoint from what the compression and loading the hash value write. -/
theorem blk_disj {a n : Nat} (h : a + n ≤ P.B) :
    ∀ r ∈ [⟨VG.Proof.Pbkdf2.X86_64.hv P s₀, P.N⟩, ⟨VG.Proof.Pbkdf2.X86_64.scr s₀, P.so⟩, VG.Proof.Pbkdf2.X86_64.stkR s₀], Region.Disjoint ⟨VG.Proof.Pbkdf2.X86_64.blk P s₀ + BitVec.ofNat 64 a, n⟩ r := by
  have := VG.Proof.Pbkdf2.X86_64.so_le hz; have := VG.Proof.Pbkdf2.X86_64.N_le hz; have := VG.Proof.Pbkdf2.X86_64.B_le hz; have hz_fits := hz.fits
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [add_ofNat]
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact (hp.stk_s.sub_right (VG.Proof.Pbkdf2.X86_64.scr_sub s₀ (by omega))).symm

/-- Loading the key's hash value at `key + o` and compressing the block into it. -/
theorem lc_ok {H : Md P.B P.N P.L} (hR : H.Reloc) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {o : Nat} (ho : o + P.N ≤ 2 * (P.N + P.B)) {s : State} (h : VG.Proof.Pbkdf2.X86_64.Regs P D W s₀ s)
    (hpad : bytesAt s.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D) {c : Prog isa}
    {Q : State → Prop}
    (k : ∀ s', VG.Proof.Pbkdf2.X86_64.Regs P D W s₀ s' → s'.gpr .r14 = s.gpr .r14 → Frame (VG.Proof.Pbkdf2.X86_64.bodyR P D s₀) s.mem s'.mem →
      Frame [⟨VG.Proof.Pbkdf2.X86_64.scr s₀, P.so⟩, ⟨VG.Proof.Pbkdf2.X86_64.hv P s₀, P.N⟩, VG.Proof.Pbkdf2.X86_64.stkR s₀] s.mem s'.mem →
      bytesAt s'.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D →
      bytesAt s'.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀) D = bytesAt s.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀) D →
      H.stateAt s'.mem (VG.Proof.Pbkdf2.X86_64.hv P s₀) =
        H.compress (H.stateAt s₀.mem (VG.Proof.Pbkdf2.X86_64.key s₀ + BitVec.ofNat 64 o)) (H.tailBlock D (bytesAt s.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀) D)) →
      WP isa c s' Q) :
    WP isa (.block (loadKey P o)) s fun s' => WP isa (.seq (compressBlock name code) c) s' Q := by
  have := VG.Proof.Pbkdf2.X86_64.so_le hz; have := VG.Proof.Pbkdf2.X86_64.N_le hz; have := VG.Proof.Pbkdf2.X86_64.B_le hz; have hz_fits := hz.fits; have hz_DN := hz.DN; have hz_pad := hz.pad
  have hz_NL := hz.NL
  rw [← List.append_nil (loadKey P o)]
  refine VG.Proof.Pbkdf2.X86_64.load_ok hz hp hR h (o := o) ho fun s₁ g₁ rd₁ wr₁ f₁ e₁ => WP.block_nil ?_
  have h₁ := h.write (fun r hr _ _ _ _ _ => g₁ r hr) rd₁ wr₁ (VG.Proof.Pbkdf2.X86_64.frame_scr (a := P.so + 48) (by omega) f₁)
  refine WP.seq (VG.Proof.Pbkdf2.X86_64.cmp_ok hz hp hf h₁ fun s₂ h₂ r14₂ f₂ e₂ => ?_)
  have fh₁ : ∀ {a n : Nat}, a + n ≤ P.B → ∀ r ∈ [(⟨VG.Proof.Pbkdf2.X86_64.hv P s₀, P.N⟩ : Region)],
      Region.Disjoint ⟨VG.Proof.Pbkdf2.X86_64.blk P s₀ + BitVec.ofNat 64 a, n⟩ r :=
    fun h' r hr => VG.Proof.Pbkdf2.X86_64.blk_disj hz hp h' r (by simp at hr; simp [hr])
  have p₁ : bytesAt s₁.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D :=
    (Memory.frame_bytesAt f₁ (fh₁ (by omega)) (by omega)).trans hpad
  have u₁ : bytesAt s₁.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀) D = bytesAt s.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀) D := by
    have := Memory.frame_bytesAt f₁ (fh₁ (a := 0) (n := D) (by omega)) (by omega); rwa [VG.Proof.Pbkdf2.X86_64.blk0] at this
  have u₂ : bytesAt s₂.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀) D = bytesAt s₁.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀) D := by
    have := Memory.frame_bytesAt f₂ (VG.Proof.Pbkdf2.X86_64.blk_disj hz hp (a := 0) (n := D) (by omega)) (by omega); rwa [VG.Proof.Pbkdf2.X86_64.blk0] at this
  rw [e₁, H.blockAt_eq (by omega) p₁, u₁] at e₂
  have f : Frame [⟨VG.Proof.Pbkdf2.X86_64.scr s₀, P.so⟩, ⟨VG.Proof.Pbkdf2.X86_64.hv P s₀, P.N⟩, VG.Proof.Pbkdf2.X86_64.stkR s₀] s.mem s₂.mem :=
    (f₁.mono (by simp)).trans (f₂.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)
  refine k s₂ h₂ (r14₂.trans (g₁ _ (by decide))) (f.sub fun r hr => ?_) f
    ((Memory.frame_bytesAt f₂ (VG.Proof.Pbkdf2.X86_64.blk_disj hz hp (by omega)) (by omega)).trans p₁) (u₂.trans u₁) e₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨VG.Proof.Pbkdf2.X86_64.scr s₀, P.so⟩, by simp, fun _ h => h⟩
  · exact VG.Proof.Pbkdf2.X86_64.sub_body (by omega) (by omega)
  · exact ⟨VG.Proof.Pbkdf2.X86_64.stkR s₀, by simp, fun _ h => h⟩

/-- The end of a step: the digest into the block, `T ← T ⊕ U` and the count. -/
theorem tail_ok {H : Md P.B P.N P.L} (hs : Shape H) {s : State} (h : VG.Proof.Pbkdf2.X86_64.Regs P D W s₀ s)
    (hpad : bytesAt s.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D) {Q : State → Prop}
    (k : ∀ s', VG.Proof.Pbkdf2.X86_64.Regs P D W s₀ s' → s'.gpr .r14 = s.gpr .r14 - (1 : BitVec 32).signExtend 64 →
      s'.zf = some (s.gpr .r14 - (1 : BitVec 32).signExtend 64 == 0) →
      Frame (VG.Proof.Pbkdf2.X86_64.bodyR P D s₀) s.mem s'.mem →
      bytesAt s'.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D →
      bytesAt s'.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀) D = (H.digest (H.stateAt s.mem (VG.Proof.Pbkdf2.X86_64.hv P s₀))).take D →
      bytesAt s'.mem (VG.Proof.Pbkdf2.X86_64.tp s₀) D =
        Spec.Pbkdf2.xorBytes (bytesAt s.mem (VG.Proof.Pbkdf2.X86_64.tp s₀) D) ((H.digest (H.stateAt s.mem (VG.Proof.Pbkdf2.X86_64.hv P s₀))).take D) → Q s') :
    WP isa (.block (Impl.Pbkdf2.X86_64.digest P D ++ (List.range (D / 4)).flatMap xorW ++
      ([.alu .sub .r14 (.imm 1)] : List Instr))) s Q := by
  have := VG.Proof.Pbkdf2.X86_64.so_le hz; have := VG.Proof.Pbkdf2.X86_64.N_le hz; have := VG.Proof.Pbkdf2.X86_64.B_le hz; have hz_fits := hz.fits; have hz_DN := hz.DN; have hz_D4 := hz.D4; have hz_W := hz.W
  have hz_pad := hz.pad; have hz_NL := hz.NL
  rw [List.append_assoc]
  refine VG.Proof.Pbkdf2.X86_64.digest_ok hz hp hs h hpad fun s₆ g₆ rd₆ wr₆ f₆ b₆ p₆ => ?_
  have h₆ := h.write (fun r hr _ _ _ _ _ => g₆ r hr) rd₆ wr₆ (VG.Proof.Pbkdf2.X86_64.frame_scr (a := P.so + 48 + P.N) (by omega) f₆)
  have hd : Region.Disjoint (VG.Proof.Pbkdf2.X86_64.tR D s₀) ⟨VG.Proof.Pbkdf2.X86_64.blk P s₀, D⟩ := hp.t_s.sub_right (VG.Proof.Pbkdf2.X86_64.scr_sub s₀ (by omega))
  have hD4 : 4 * (D / 4) = D := by omega
  refine VG.Proof.Pbkdf2.X86_64.xor_ok hd (by omega_using [hz_W, hz_DN, hz_fits]) (D / 4) (by omega_using []) _ s₆ _ h₆.rbp h₆.r13
    (fun j hj => by
      obtain ⟨r, hr, hc⟩ := VG.Proof.Pbkdf2.X86_64.in_blk hz hp h₆.wr (a := 4 * j) (n := 4) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (fun j hj => ⟨VG.Proof.Pbkdf2.X86_64.tR D s₀, by simp [h₆.wr, hp.wr], Offset.contains_base _ (by omega) (by omega)⟩)
    fun s₇ g₇ rd₇ wr₇ m₇ => ?_
  rw [hD4] at m₇
  have hxl : (Spec.Pbkdf2.xorBytes (bytesAt s₆.mem (VG.Proof.Pbkdf2.X86_64.tp s₀) D) (bytesAt s₆.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀) D)).length = D := by
    rw [Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
  have f₇ : Frame [VG.Proof.Pbkdf2.X86_64.tR D s₀] s₆.mem s₇.mem := by
    rw [m₇]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
  have h₇ := h₆.write (fun r hr _ _ _ _ _ => g₇ r hr) rd₇ wr₇ (f₇.mono (by simp))
  refine wp_subi fun s₈ u₈ z₈ => WP.block_nil ?_
  have h₈ := h₇.write (fun r _ _ _ _ _ hr => u₈.other r hr) u₈.rd u₈.wr (by rw [u₈.mem]; exact Frame.refl _ _)
  have r14₇ : s₇.gpr .r14 = s.gpr .r14 := by rw [g₇ _ (by decide), g₆ _ (by decide)]
  have hT₆ : bytesAt s₆.mem (VG.Proof.Pbkdf2.X86_64.tp s₀) D = bytesAt s.mem (VG.Proof.Pbkdf2.X86_64.tp s₀) D :=
    Memory.frame_bytesAt f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.t_s.sub_right (VG.Proof.Pbkdf2.X86_64.scr_sub s₀ (a := P.so + 48 + P.N) (n := P.N) (by omega))) (by omega_using [hz_W, hz_DN, hz_fits])
  refine k s₈ h₈ (by rw [u₈.gpr, r14₇]) (by rw [z₈, r14₇]) ?_ ?_ ?_ ?_
  · rw [u₈.mem]
    refine (f₆.sub fun r hr => ?_).trans (f₇.mono (by simp))
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Proof.Pbkdf2.X86_64.sub_body (by omega) (by omega_using [hz_NL])
  · rw [u₈.mem]
    exact (Memory.frame_bytesAt f₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.t_s.sub_right (by rw [add_ofNat]; exact VG.Proof.Pbkdf2.X86_64.scr_sub s₀ (by omega_using [hz_pad, hz_fits]))).symm) (by omega_using [this])).trans p₆
  · rw [u₈.mem, m₇, bytesAt_writeBytes_sep _ _ (hd.symm.sep (Region.contains_self _ _) (by
      rw [hxl]; exact Region.contains_self _ _)) (by omega_using [hz_W, hz_DN, hz_fits]), b₆]
  · rw [u₈.mem, m₇, bytesAt_writeBytes_self' hxl (by omega), hT₆, b₆]

omit hz hp in
theorem iterate_succ (f : List Byte → List Byte) (n : Nat) (u t : List Byte) :
    Spec.Pbkdf2.iterate f (n + 1) u t = Spec.Pbkdf2.iterate f n (f u) (Spec.Pbkdf2.xorBytes t (f u)) := rfl

theorem body_ok {H : Md P.B P.N P.L} (hs : Shape H) (hR : H.Reloc) {name : String} {code : Prog isa}
    (hf : CalleeOk H code) {r : Nat} {s : State} (h : VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀ (r + 1) s) :
    WP isa (body P D name code) s fun s' => eval .ne s' = some (r != 0) ∧ VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀ r s' := by
  have := VG.Proof.Pbkdf2.X86_64.so_le hz; have := VG.Proof.Pbkdf2.X86_64.N_le hz; have := VG.Proof.Pbkdf2.X86_64.B_le hz; have hz_fits := hz.fits; have hz_DN := hz.DN; have hz_pad := hz.pad
  have hz_NL := hz.NL
  unfold body
  refine WP.seq (VG.Proof.Pbkdf2.X86_64.lc_ok hz hp hR hf (o := 0) (by omega_using []) h.toRegs h.pad fun s₂ h₂ r14₂ f₂ g₂ p₂ _ e₂ => ?_)
  refine WP.seq (VG.Proof.Pbkdf2.X86_64.digest_ok hz hp hs h₂ p₂ fun s₃ g₃ rd₃ wr₃ f₃ b₃ p₃ => ?_)
  have h₃ := h₂.write (fun r hr _ _ _ _ _ => g₃ r hr) rd₃ wr₃ (VG.Proof.Pbkdf2.X86_64.frame_scr (a := P.so + 48 + P.N) (by omega) f₃)
  refine VG.Proof.Pbkdf2.X86_64.lc_ok hz hp hR hf (o := P.N + P.B) (by omega) h₃ p₃ fun s₅ h₅ r14₅ f₅ g₅ p₅ _ e₅ => ?_
  refine VG.Proof.Pbkdf2.X86_64.tail_ok hz hp hs h₅ p₅ fun s₈ h₈ r14₈ z₈ f₈ p₈ b₈ t₈ => ?_
  rw [e₅, b₃, e₂, show VG.Proof.Pbkdf2.X86_64.key s₀ + BitVec.ofNat 64 0 = VG.Proof.Pbkdf2.X86_64.key s₀ by simp] at b₈ t₈
  have r14₅' : s₅.gpr .r14 = BitVec.ofNat 64 (r + 1) := by
    rw [r14₅, g₃ _ (by decide), r14₂, h.r14]
  have hlt : r + 1 < 2 ^ 64 := by
    have h_le := h.le; have := ((s₀.gpr .rdx).setWidth 32).isLt; simp at *; omega_using [h_le]
  have e₈ : s₅.gpr .r14 - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 r := by
    rw [r14₅', show (1 : BitVec 32).signExtend 64 = 1 from rfl, ofNat_pred (by omega)]; rfl
  have fb : Frame (VG.Proof.Pbkdf2.X86_64.bodyR P D s₀) s.mem s₈.mem :=
    ((f₂.trans (f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Pbkdf2.X86_64.sub_body (by omega) (by omega))).trans f₅).trans f₈
  have hT₅ : bytesAt s₅.mem (VG.Proof.Pbkdf2.X86_64.tp s₀) D = bytesAt s.mem (VG.Proof.Pbkdf2.X86_64.tp s₀) D := by
    refine Memory.frame_bytesAt (rs := [⟨VG.Proof.Pbkdf2.X86_64.scr s₀, P.so⟩, ⟨VG.Proof.Pbkdf2.X86_64.hv P s₀, P.N + P.B⟩, VG.Proof.Pbkdf2.X86_64.stkR s₀])
      (((g₂.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)).trans (g₅.sub fun r hr => ?_)) (fun r hr => ?_) (by omega)
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    · rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨VG.Proof.Pbkdf2.X86_64.hv P s₀, P.N + P.B⟩, by simp, Region.sub_prefix (by omega)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · subst hr; exact ⟨⟨VG.Proof.Pbkdf2.X86_64.hv P s₀, P.N + P.B⟩, by simp, Offset.sub _ (by omega) (by omega_using [hz_NL])⟩
    · rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨VG.Proof.Pbkdf2.X86_64.hv P s₀, P.N + P.B⟩, by simp, Region.sub_prefix (by omega)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · rcases hr with rfl | rfl | rfl
      · exact hp.t_s.sub_right (Region.sub_prefix (by omega))
      · exact hp.t_s.sub_right (VG.Proof.Pbkdf2.X86_64.scr_sub s₀ (by omega))
      · exact hp.stk_t.symm
  rw [hT₅] at t₈
  refine ⟨?_, h₈, by rw [r14₈, e₈], VG.Proof.Pbkdf2.X86_64.saved_frame hz hp h.saved fb, p₈, by have h_le := h.le; omega, ?_⟩
  · simp only [eval, z₈, e₈, Option.map_some, ofNat_beq_zero (by omega : r < 2 ^ 64)]
    cases r <;> rfl
  · rw [h.val, VG.Proof.Pbkdf2.X86_64.iterate_succ, b₈, t₈]; rfl
theorem loop_ok {H : Md P.B P.N P.L} (hs : Shape H) (hR : H.Reloc) {name : String} {code : Prog isa}
    (hf : CalleeOk H code) {n : Nat} {s : State} (h : VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀ n s) (hz' : s.zf = some (decide (n = 0))) :
    WP isa (.ite .e (.block []) (.loop (body P D name code) .ne)) s (VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀ 0) := by
  refine WP.ite (decide (n = 0)) hz' (fun hb => ?_) (fun hb => ?_)
  · obtain rfl : n = 0 := by simpa using hb
    exact WP.block_nil h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hb; omega⟩
    refine WP.loop (fun m s => VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀ (m + 1) s)
      (fun m s hs' => WP.mono (VG.Proof.Pbkdf2.X86_64.body_ok hz hp hs hR hf hs') fun s' ⟨he, hi⟩ => ?_) m s h
    cases m with
    | zero => exact .inl ⟨he, hi⟩
    | succ m => exact .inr ⟨he, m, by omega, hi⟩

end

/-! ## The prologue -/

/-- After saving our caller's registers and setting up ours. -/
structure Setup (P : Params) (D W : Nat) (s₀ s : State) : Prop extends VG.Proof.Pbkdf2.X86_64.Regs P D W s₀ s where
  r14 : s.gpr .r14 = BitVec.ofNat 64 (VG.Proof.Pbkdf2.X86_64.nn s₀)
  rdi : s.gpr .rdi = VG.Proof.Pbkdf2.X86_64.key s₀
  rsi : s.gpr .rsi = VG.Proof.Pbkdf2.X86_64.up s₀
  mem : s.mem = saveMem P s₀ .r8

section
variable {P : Params} {D W : Nat} (hz : VG.Proof.Pbkdf2.X86_64.Sizes P D W) {s₀ : State} (hp : VG.Proof.Pbkdf2.X86_64.Pre P D W s₀)
include hz hp

theorem setup_ok {rest : List Instr} {Q : State → Prop} (k : ∀ s, VG.Proof.Pbkdf2.X86_64.Setup P D W s₀ s → WP isa (.block rest) s Q) :
    WP isa (.block (save P .r8 ++
      ([.mov .r15 (.reg .r8), .mov .r12 (.reg .rdi), .mov .r13 (.reg .rcx), .mov32 .r14 (.reg .rdx),
        .mov .rbx (.reg .r8), .alu .add .rbx (.imm (BitVec.ofNat 32 (hvO P))),
        .mov .rbp (.reg .r8), .alu .add .rbp (.imm (BitVec.ofNat 32 (blkO P)))] : List Instr) ++ rest)) s₀ Q := by
  have := VG.Proof.Pbkdf2.X86_64.so_le hz; have := VG.Proof.Pbkdf2.X86_64.N_le hz; have := VG.Proof.Pbkdf2.X86_64.B_le hz; have hz_fits := hz.fits; have hz_W := hz.W
  have o : ∀ d : Nat, d + 8 ≤ 8 * W → InRegions s₀.wr (VG.Proof.Pbkdf2.X86_64.scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => by rw [ofInt_natCast]; exact VG.Proof.Pbkdf2.X86_64.in_scr hz hp rfl hd
  rw [save_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_store (a := VG.Proof.Pbkdf2.X86_64.scr s₀ + BitVec.ofInt 64 ((P.so : Nat) : Int)) rfl (o _ (by omega))
    fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  refine wp_store (a := VG.Proof.Pbkdf2.X86_64.scr s₀ + BitVec.ofInt 64 ((P.so + 8 : Nat) : Int)) (by simp only [State.ea, at_, g₁])
    (by rw [wr₁]; exact o _ (by omega_using [hz_fits])) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_store (a := VG.Proof.Pbkdf2.X86_64.scr s₀ + BitVec.ofInt 64 ((P.so + 16 : Nat) : Int))
    (by simp only [State.ea, at_, g₂, g₁]) (by rw [wr₂, wr₁]; exact o _ (by omega)) fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  refine wp_store (a := VG.Proof.Pbkdf2.X86_64.scr s₀ + BitVec.ofInt 64 ((P.so + 24 : Nat) : Int))
    (by simp only [State.ea, at_, g₃, g₂, g₁]) (by rw [wr₃, wr₂, wr₁]; exact o _ (by omega))
    fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  refine wp_store (a := VG.Proof.Pbkdf2.X86_64.scr s₀ + BitVec.ofInt 64 ((P.so + 32 : Nat) : Int))
    (by simp only [State.ea, at_, g₄, g₃, g₂, g₁])
    (by rw [wr₄, wr₃, wr₂, wr₁]; exact o _ (by omega)) fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  refine wp_store (a := VG.Proof.Pbkdf2.X86_64.scr s₀ + BitVec.ofInt 64 ((P.so + 40 : Nat) : Int))
    (by simp only [State.ea, at_, g₅, g₄, g₃, g₂, g₁])
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]; exact o _ (by omega)) fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  have hg₆ : s₆.gpr = s₀.gpr := by rw [g₆, g₅, g₄, g₃, g₂, g₁]
  have hm₆ : s₆.mem = saveMem P s₀ .r8 := by
    rw [m₆, m₅, m₄, m₃, m₂, m₁]; simp only [saveMem, g₅, g₄, g₃, g₂, g₁]
  refine wp_mov fun s₇ u₇ _ _ => wp_mov fun s₈ u₈ _ _ => wp_mov fun s₉ u₉ _ _ => VG.Proof.Pbkdf2.X86_64.wp_mov32r fun s₁₀ u₁₀ =>
    wp_mov fun s₁₁ u₁₁ _ _ => wp_addi fun s₁₂ u₁₂ => wp_mov fun s₁₃ u₁₃ _ _ => wp_addi fun s₁₄ u₁₄ => ?_
  have G : ∀ r, r ≠ .r15 → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → r ≠ .rbx → r ≠ .rbp → s₁₄.gpr r = s₀.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => by
      rw [u₁₄.other r h6, u₁₃.other r h6, u₁₂.other r h5, u₁₁.other r h5, u₁₀.other r h4, u₉.other r h3,
        u₈.other r h2, u₇.other r h1, hg₆]
  have hm : s₁₄.mem = saveMem P s₀ .r8 := by
    rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, hm₆]
  refine k s₁₄ ⟨⟨by rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁], ?_, ?_,
    ?_, ?_, ?_, G _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_⟩, ?_,
    G _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    G _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hm⟩
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.gpr, u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), hg₆, hvO, sx_ofNat (by omega)]
  · rw [u₁₄.gpr, u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), hg₆, blkO, sx_ofNat (by omega)]
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), hg₆]
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), hg₆]
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, hg₆]
  · rw [hm]; exact (saveMem_frame hz.dims).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Pbkdf2.X86_64.scR W s₀, by simp, Region.sub_prefix (by omega)⟩
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), hg₆]
    apply BitVec.eq_of_toNat_eq
    have := ((s₀.gpr .rdx).setWidth 32).isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, VG.Proof.Pbkdf2.X86_64.nn]

/-- Writing `U`, the padding and the length field into the block. -/
theorem fill_ok {H : Md P.B P.N P.L} (hs : Shape H) (hok : H.lenOk (P.B + D)) {s : State}
    (h : VG.Proof.Pbkdf2.X86_64.Setup P D W s₀ s) :
    WP isa (.block ((List.range (D / 4)).flatMap (Impl.Pbkdf2.X86_64.cp32 .rsi .rbp 0 0) ++
      Impl.Pbkdf2.X86_64.padLen P D ++ ([.mov .r12 (.reg .rdi), .alu .test .r14 (.reg .r14)] : List Instr))) s
      fun s' => VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀ (VG.Proof.Pbkdf2.X86_64.nn s₀) s' ∧ s'.zf = some (decide (VG.Proof.Pbkdf2.X86_64.nn s₀ = 0)) := by
  have := VG.Proof.Pbkdf2.X86_64.so_le hz; have := VG.Proof.Pbkdf2.X86_64.N_le hz; have := VG.Proof.Pbkdf2.X86_64.B_le hz; have hz_fits := hz.fits; have hz_DN := hz.DN; have hz_pad := hz.pad
  have hz_NL := hz.NL; have hz_D4 := hz.D4; have hz_L4 := hz.L4; have hz_W := hz.W; have := VG.Proof.Pbkdf2.X86_64.B_ge hz
  have : P.B % 4 = 0 := by rcases hz.dims.B with h | h <;> omega
  have hD4 : 4 * (D / 4) = D := by omega
  have u0 : VG.Proof.Pbkdf2.X86_64.up s₀ + BitVec.ofNat 64 0 = VG.Proof.Pbkdf2.X86_64.up s₀ := by simp
  simp only [List.append_assoc]
  refine VG.Proof.Pbkdf2.X86_64.copy32_ok (by decide) (by decide) 0 0 (D / 4) _ s _ (fun j hj => ?_) (fun j hj => ?_) ?_ (by omega)
    fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  · rw [h.rsi, h.rd, hp.rd, u0]
    exact ⟨VG.Proof.Pbkdf2.X86_64.uR D s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [h.rbp, VG.Proof.Pbkdf2.X86_64.blk0]; exact VG.Proof.Pbkdf2.X86_64.in_blk hz hp h.wr (by omega_using [hj, hz_pad])
  · rw [h.rsi, h.rbp, VG.Proof.Pbkdf2.X86_64.blk0, u0, hD4]
    exact hp.u_s.sep (Region.contains_self _ _) (Offset.contains_base _ (by omega_using [hz_pad, hz_fits]) (by omega_using [hz_W, hz_fits]))
  rw [h.rbp, h.rsi, VG.Proof.Pbkdf2.X86_64.blk0, u0, hD4] at m₁
  refine VG.Proof.Pbkdf2.X86_64.padLen_ok hs hok hz.D4 hz.L4 this (by omega) (by omega) (s := s₁) (p := VG.Proof.Pbkdf2.X86_64.blk P s₀)
    (by rw [g₁ _ (by decide), h.rbp])
    (by rw [g₁ _ (by decide), h.rbx, add_ofNat, add_ofNat,
      show P.so + 48 + (P.N + P.B - P.L) = P.so + 48 + P.N + (P.B - P.L) by omega_using [hz_pad]])
    (fun a n h' => VG.Proof.Pbkdf2.X86_64.in_blk hz hp (wr₁.trans h.wr) h') fun s₄ g₄ rd₄ wr₄ f₄ p₄ u₄ => ?_
  refine wp_mov fun s₅ u₅ _ _ => wp_test fun s₆ g₆ m₆ rd₆ wr₆ z₆ => WP.block_nil ?_
  have hG : ∀ r, r ≠ .rax → r ≠ .r12 → s₆.gpr r = s.gpr r := fun r h1 h2 => by
    rw [g₆, u₅.other r h2, g₄ r h1 h2, g₁ r h1]
  have f₁ : Frame [⟨VG.Proof.Pbkdf2.X86_64.blk P s₀, P.B⟩] s.mem s₁.mem := by
    rw [m₁, h.mem]; refine VG.WriteBytes.writeBytes_frame _ _ _ ?_
    rw [bytesAt_length]
    have := Offset.contains_base (VG.Proof.Pbkdf2.X86_64.blk P s₀) (d := 0) (n := D) (k := P.B) (by omega_using [hz_pad]) (by omega)
    rwa [VG.Proof.Pbkdf2.X86_64.blk0] at this
  have fM : Frame [⟨VG.Proof.Pbkdf2.X86_64.blk P s₀, P.B⟩] s.mem s₆.mem := by
    rw [m₆, u₅.mem]; exact f₁.trans f₄
  have fB : Frame (VG.Proof.Pbkdf2.X86_64.bodyR P D s₀) s.mem s₆.mem := fM.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Pbkdf2.X86_64.sub_body (by omega) (by omega)
  refine ⟨⟨⟨by rw [rd₆, u₅.rd, rd₄, rd₁, h.rd], by rw [wr₆, u₅.wr, wr₄, wr₁, h.wr],
    by rw [hG _ (by decide) (by decide), h.rbx], by rw [hG _ (by decide) (by decide), h.rbp],
    by rw [g₆, u₅.gpr, g₄ _ (by decide) (by decide), g₁ _ (by decide), h.rdi],
    by rw [hG _ (by decide) (by decide), h.r13], by rw [hG _ (by decide) (by decide), h.r15],
    by rw [hG _ (by decide) (by decide), h.rsp], h.frame.trans (VG.Proof.Pbkdf2.X86_64.frame_scr (a := P.so + 48 + P.N) (by omega) fM)⟩,
    by rw [hG _ (by decide) (by decide), h.r14], VG.Proof.Pbkdf2.X86_64.saved_frame hz hp (h.mem ▸ saveMem_saved hz.dims) fB,
    by rw [m₆, u₅.mem]; exact p₄, Nat.le_refl _, ?_⟩, ?_⟩
  · -- `U` and `T`.
    have hU : bytesAt s₆.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀) D = bytesAt s₀.mem (VG.Proof.Pbkdf2.X86_64.up s₀) D := by
      rw [m₆, u₅.mem, u₄, m₁, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega), h.mem]
      refine Memory.frame_bytesAt (saveMem_frame hz.dims) (fun r hr => ?_) (by omega)
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.u_s.sub_right (Region.sub_prefix (by omega_using [hz_fits]))
    have hT : bytesAt s₆.mem (VG.Proof.Pbkdf2.X86_64.tp s₀) D = bytesAt s₀.mem (VG.Proof.Pbkdf2.X86_64.tp s₀) D := by
      refine Memory.frame_bytesAt (((saveMem_frame (s₀ := s₀) (b := .r8) hz.dims).mono
        (rs' := [⟨VG.Proof.Pbkdf2.X86_64.scr s₀, P.so + 48⟩, ⟨VG.Proof.Pbkdf2.X86_64.blk P s₀, P.B⟩]) (by simp)).trans
        ((h.mem ▸ fM).mono (by simp))) (fun r hr => ?_) (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.t_s.sub_right (Region.sub_prefix (by omega))
      · exact hp.t_s.sub_right (VG.Proof.Pbkdf2.X86_64.scr_sub s₀ (by omega))
    rw [hU, hT]
  · have r14₅ : s₅.gpr .r14 = BitVec.ofNat 64 (VG.Proof.Pbkdf2.X86_64.nn s₀) := by
      rw [u₅.other _ (by decide), g₄ _ (by decide) (by decide), g₁ _ (by decide), h.r14]
    rw [z₆, r14₅, BitVec.and_self, ofNat_beq_zero (by have := ((s₀.gpr .rdx).setWidth 32).isLt; simp [VG.Proof.Pbkdf2.X86_64.nn]; omega_using [])]
theorem prologue_ok {H : Md P.B P.N P.L} (hs : Shape H) (hok : H.lenOk (P.B + D)) :
    WP isa (.block (prologue P D)) s₀ fun s => VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀ (VG.Proof.Pbkdf2.X86_64.nn s₀) s ∧ s.zf = some (decide (VG.Proof.Pbkdf2.X86_64.nn s₀ = 0)) := by
  have := VG.Proof.Pbkdf2.X86_64.setup_ok hz hp (rest := (List.range (D / 4)).flatMap (Impl.Pbkdf2.X86_64.cp32 .rsi .rbp 0 0) ++
    Impl.Pbkdf2.X86_64.padLen P D ++ [.mov .r12 (.reg .rdi), .alu .test .r14 (.reg .r14)])
    fun s h => VG.Proof.Pbkdf2.X86_64.fill_ok hz hp hs hok h
  unfold prologue
  simpa only [List.append_assoc] using this

set_option simprocs false in
/-- Restoring our caller's registers from the scratch space. -/
theorem restore_ok {s : State} (hwr : s.wr = s₀.wr) (h15 : s.gpr .r15 = VG.Proof.Pbkdf2.X86_64.scr s₀)
    (hsv : Saved P s₀ .r8 s.mem) :
    WP isa (.block (restore P)) s fun s' =>
      s'.mem = s.mem ∧ s'.gpr .rsp = s.gpr .rsp ∧ ∀ r ∈ calleeSaved, r ≠ .rsp → s'.gpr r = s₀.gpr r := by
  have := VG.Proof.Pbkdf2.X86_64.so_le hz; have := VG.Proof.Pbkdf2.X86_64.N_le hz; have := VG.Proof.Pbkdf2.X86_64.B_le hz; have hz_fits := hz.fits; have hz_W := hz.W
  have i : ∀ d : Nat, d + 8 ≤ P.so + 48 → InRegions (s.rd ++ s.wr) (VG.Proof.Pbkdf2.X86_64.scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => by
      rw [ofInt_natCast]
      obtain ⟨r, hr, hc⟩ := VG.Proof.Pbkdf2.X86_64.in_scr hz hp hwr (a := d) (n := 8) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
  have sv : ∀ r d, (r, d) ∈ saved P →
      s.mem.readW (VG.Proof.Pbkdf2.X86_64.scr s₀ + BitVec.ofInt 64 ((d : Nat) : Int)) 64 = s₀.gpr r :=
    fun r d hrd => hsv (r, d) hrd
  have i0 := i P.so (by omega); have i1 := i (P.so + 8) (by omega); have i2 := i (P.so + 16) (by omega)
  have i3 := i (P.so + 24) (by omega); have i4 := i (P.so + 32) (by omega); have i5 := i (P.so + 40) (by omega)
  have g0 := sv .rbx P.so (by simp only [saved, List.mem_cons, true_or]); have g1 := sv .rbp (P.so + 8) (by simp only [saved, List.mem_cons, true_or, or_true])
  have g2 := sv .r12 (P.so + 16) (by simp only [saved, List.mem_cons, true_or, or_true]); have g3 := sv .r13 (P.so + 24) (by simp only [saved, List.mem_cons, true_or, or_true])
  have g4 := sv .r14 (P.so + 32) (by simp only [saved, List.mem_cons, true_or, or_true]); have g5 := sv .r15 (P.so + 40) (by simp only [saved, List.mem_cons, true_or, or_true])
  apply WP.of_runBlock
  rw [restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, ea_at, State.load64,
    State.setReg, h15, i0, i1, i2, i3, i4, i5, ite_true, ite_false, g0, g1, g2, g3, g4, g5,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, by simp (config := {decide := true}), fun r hr hne => ?_⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) at hne ⊢

omit hz hp in
/-- The final `T` is PBKDF2's, for a key as the contract requires. -/
theorem post_eq {H : Md P.B P.N P.L} {S : StreamingHash} {iv : H.HV} (hl : H.Link S iv D) {m : Mem}
    (hT : bytesAt m (VG.Proof.Pbkdf2.X86_64.tp s₀) D =
      Spec.Pbkdf2.iterate (VG.Proof.Pbkdf2.X86_64.stepM P D H s₀) (VG.Proof.Pbkdf2.X86_64.nn s₀) (bytesAt s₀.mem (VG.Proof.Pbkdf2.X86_64.up s₀) D) (bytesAt s₀.mem (VG.Proof.Pbkdf2.X86_64.tp s₀) D))
    {k0 : List Byte} (hk : k0.length = S.H.blockSize) (hi : S.Repr s₀.mem (VG.Proof.Pbkdf2.X86_64.key s₀) (xorPad k0 ipad))
    (ho : S.Repr s₀.mem (VG.Proof.Pbkdf2.X86_64.key s₀ + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad)) :
    bytesAt m (VG.Proof.Pbkdf2.X86_64.tp s₀) S.digestBytes =
      Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) (VG.Proof.Pbkdf2.X86_64.nn s₀) (bytesAt s₀.mem (VG.Proof.Pbkdf2.X86_64.up s₀) S.digestBytes)
        (bytesAt s₀.mem (VG.Proof.Pbkdf2.X86_64.tp s₀) S.digestBytes) := by
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
    (h : VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀ 0 s) :
    WP isa (.block (restore P)) s fun s' => gprPreserved s₀ s' ∧ (VG.Proof.Pbkdf2.X86_64.iterK S W).post s₀ s' := by
  refine WP.mono (VG.Proof.Pbkdf2.X86_64.restore_ok hz hp h.wr h.r15 h.saved) fun s' ⟨hm, hsp, hcs⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun k0 hk hi ho => ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; rw [hsp, h.rsp]
    · exact hcs r hr hr'
  · rw [hm]
    exact h.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_t, hp.ret_s, VG.Proof.Pbkdf2.X86_64.ret_stk s₀⟩) (by decide)
  · rw [hm]; exact VG.Proof.Pbkdf2.X86_64.post_eq hl h.val.symm hk hi ho
end

/-! ## Correctness -/

/-- What the proof needs of a hash function, with its code's `Params`, a
`D`-byte digest and `W` words of scratch space: the sizes, the length field
and digest of its code, that its hash value depends only on the bytes it is
stored in, that the length field of a `B + D`-byte message is its byte
count's, and that it is the hash function `S` of the specification. -/
structure HashOk (P : Params) (D W : Nat) (S : StreamingHash) (H : Md P.B P.N P.L) (iv : H.HV) : Prop where
  sizes : VG.Proof.Pbkdf2.X86_64.Sizes P D W
  shape : Shape H
  reloc : H.Reloc
  lenOk : H.lenOk (P.B + D)
  link : H.Link S iv D

theorem correct {P : Params} {D W : Nat} {S : StreamingHash} {H : Md P.B P.N P.L} {iv : H.HV}
    (ho : VG.Proof.Pbkdf2.X86_64.HashOk P D W S H iv) {name : String} {code : Prog isa} (hf : CalleeOk H code) {s₀ : State}
    (hp : VG.Proof.Pbkdf2.X86_64.Pre P D W s₀) :
    WP isa (iterate P D name code) s₀ fun s' => gprPreserved s₀ s' ∧ (VG.Proof.Pbkdf2.X86_64.iterK S W).post s₀ s' := by
  unfold iterate
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.X86_64.prologue_ok ho.sizes hp ho.shape ho.lenOk) fun s₁ ⟨h, hz'⟩ => ?_)
  exact WP.seq (WP.mono (VG.Proof.Pbkdf2.X86_64.loop_ok ho.sizes hp ho.shape ho.reloc hf h hz') fun s₂ h₂ =>
    VG.Proof.Pbkdf2.X86_64.epilogue_ok ho.sizes hp ho.link h₂)

/-- `iterate` is correct and keeps what the calling convention requires, if it
never loads MXCSR. -/
theorem iterate_ok {P : Params} {D W : Nat} {S : StreamingHash} {H : Md P.B P.N P.L} {iv : H.HV}
    (ho : VG.Proof.Pbkdf2.X86_64.HashOk P D W S H iv) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hm : (iterate P D name code).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (hs : (VG.Proof.Pbkdf2.X86_64.iterK S W).pre s) :
    ∃ t s', Exec isa (iterate P D name code) s t s' ∧ abiPreserved s s' ∧ (VG.Proof.Pbkdf2.X86_64.iterK S W).post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.Pbkdf2.X86_64.correct ho hf (VG.Proof.Pbkdf2.X86_64.pre_of ho.link.hS ho.link.hD hs)
  exact ⟨t, s', he, abiPreserved_of_exec hm he h.1, h.2⟩

end VG.Proof.Pbkdf2.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.X86_64.IterateCT`. -/
section

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on x86-64: constant time

This holds for any compression function (`CalleeOk`), so it is proven once
for every implementation. The taint analysis cannot prove it without
looking into the compression function: it saves and restores our registers
in memory it also writes secrets to, so across a call the analysis forgets
that our pointers are public. So we relate two runs (`RelCT`): at every
point, correctness determines our registers from the public arguments
alone, so they agree; between the calls, the taint analysis proves each
block constant time from that (`Checks`, evaluated for each hash function,
since the code depends on its sizes); and the calls are constant time by
the compression function's own proof (`compressAt_rel`).
-/

namespace VG.Proof.Pbkdf2.X86_64

open VG VG.X86_64
open VG.Impl.MdStream.X86_64 (Params restore compressAt)
open VG.Impl.Pbkdf2.X86_64 (loadKey xorW compressBlock body prologue iterate)
open VG.Proof.MdStream (Md)
open VG.Proof.MdStream.X86_64 (Shape CalleeOk compressAt_rel wp_mov)
open VG.Spec.Sha256 (bytesAt)
open VG.Spec.Hmac (StreamingHash)

/-- The registers the blocks between the calls use. -/
abbrev regsS : List Reg := [.rbx, .rbp, .r12, .r13, .r15, .rsp, .r14]

/-- The taint checks of the pieces of `iterate` between its calls, which
depend on the hash function's sizes, its length field and its digest. -/
structure Checks (P : Params) (D : Nat) : Prop where
  pro : ∃ hc, (taint.check (Taint.ofRegs [.rdi, .rsi, .rcx, .r8, .rsp]) (.block (prologue P D)) hc).isSome = true
  load : ∃ hc, (taint.check (Taint.ofRegs VG.Proof.Pbkdf2.X86_64.regsS) (.block (loadKey P 0)) hc).isSome = true
  arg : ∃ hc, (taint.check (Taint.ofRegs VG.Proof.Pbkdf2.X86_64.regsS) (.block [.mov .rsi (.reg .rbp)]) hc).isSome = true
  mid : ∃ hc, (taint.check (Taint.ofRegs VG.Proof.Pbkdf2.X86_64.regsS)
    (.block (Impl.Pbkdf2.X86_64.digest P D ++ loadKey P (P.N + P.B))) hc).isSome = true
  fin : ∃ hc, (taint.check (Taint.ofRegs VG.Proof.Pbkdf2.X86_64.regsS) (.block (Impl.Pbkdf2.X86_64.digest P D ++
    (List.range (D / 4)).flatMap xorW ++ [.alu .sub .r14 (.imm 1)])) hc).isSome = true
  epi : ∃ hc, (taint.check (Taint.ofRegs [.r15]) (.block (restore P)) hc).isSome = true
  ite : ∃ hc, (taint.check (Taint.ofRegs []) (.block []) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : (s₀.gpr .rdx).setWidth 32 = (s₀'.gpr .rdx).setWidth 32
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

theorem PubEq.nn {s₀ s₀' : State} (hq : VG.Proof.Pbkdf2.X86_64.PubEq s₀ s₀') : VG.Proof.Pbkdf2.X86_64.nn s₀ = VG.Proof.Pbkdf2.X86_64.nn s₀' :=
  congrArg BitVec.toNat hq.rdx

/-- The state during a step, with `v` in `r14`. -/
structure St (P : Params) (D W : Nat) (H : Md P.B P.N P.L) (s₀ : State) (v : Addr) (s : State) : Prop
    extends VG.Proof.Pbkdf2.X86_64.Regs P D W s₀ s where
  r14 : s.gpr .r14 = v
  pad : bytesAt s.mem (VG.Proof.Pbkdf2.X86_64.blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D

section
variable {P : Params} {D W : Nat} {H : Md P.B P.N P.L}

/-- The registers the blocks use agree in two runs. -/
theorem St.agree {s₀ s₀' : State} (hq : VG.Proof.Pbkdf2.X86_64.PubEq s₀ s₀') {v : Addr} {s s' : State} (h : VG.Proof.Pbkdf2.X86_64.St P D W H s₀ v s)
    (h' : VG.Proof.Pbkdf2.X86_64.St P D W H s₀' v s') : ∀ r ∈ VG.Proof.Pbkdf2.X86_64.regsS, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, VG.Proof.Pbkdf2.X86_64.hv, VG.Proof.Pbkdf2.X86_64.hv, VG.Proof.Pbkdf2.X86_64.scr, VG.Proof.Pbkdf2.X86_64.scr, hq.r8]
  · rw [h.rbp, h'.rbp, VG.Proof.Pbkdf2.X86_64.blk, VG.Proof.Pbkdf2.X86_64.blk, VG.Proof.Pbkdf2.X86_64.scr, VG.Proof.Pbkdf2.X86_64.scr, hq.r8]
  · rw [h.r12, h'.r12, VG.Proof.Pbkdf2.X86_64.key, VG.Proof.Pbkdf2.X86_64.key, hq.rdi]
  · rw [h.r13, h'.r13, VG.Proof.Pbkdf2.X86_64.tp, VG.Proof.Pbkdf2.X86_64.tp, hq.rcx]
  · rw [h.r15, h'.r15, VG.Proof.Pbkdf2.X86_64.scr, VG.Proof.Pbkdf2.X86_64.scr, hq.r8]
  · rw [h.rsp, h'.rsp, hq.rsp]
  · rw [h.r14, h'.r14]

theorem St.of_inv {s₀ : State} {r : Nat} {s : State} (h : VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀ (r + 1) s) :
    VG.Proof.Pbkdf2.X86_64.St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s :=
  ⟨h.toRegs, h.r14, h.pad⟩

variable (hz : VG.Proof.Pbkdf2.X86_64.Sizes P D W) {s₀ : State} (hp : VG.Proof.Pbkdf2.X86_64.Pre P D W s₀) {v : Addr}
include hz hp

/-! ## What each piece of a step does, in one run -/

theorem load_st (hR : H.Reloc) {o : Nat} (ho : o + P.N ≤ 2 * (P.N + P.B)) {s : State} (h : VG.Proof.Pbkdf2.X86_64.St P D W H s₀ v s) :
    WP isa (.block (loadKey P o)) s (VG.Proof.Pbkdf2.X86_64.St P D W H s₀ v) := by
  have := VG.Proof.Pbkdf2.X86_64.so_le hz; have := VG.Proof.Pbkdf2.X86_64.N_le hz; have := VG.Proof.Pbkdf2.X86_64.B_le hz; have := hz.fits; have := hz.DN; have := hz.pad
  have := hz.NL
  rw [← List.append_nil (loadKey P o)]
  exact VG.Proof.Pbkdf2.X86_64.load_ok hz hp hR h.toRegs ho fun s' g rd wr f _ => WP.block_nil
    ⟨h.toRegs.write (fun r hr _ _ _ _ _ => g r hr) rd wr (VG.Proof.Pbkdf2.X86_64.frame_scr (a := P.so + 48) (by omega) f),
      (g _ (by decide)).trans h.r14,
      (Memory.frame_bytesAt f (fun r hr => VG.Proof.Pbkdf2.X86_64.blk_disj hz hp (by omega) r (by simp at hr; simp [hr])) (by omega)).trans
        h.pad⟩

theorem cmp_st {name : String} {code : Prog isa} (hf : CalleeOk H code) {s : State} (h : VG.Proof.Pbkdf2.X86_64.St P D W H s₀ v s) :
    WP isa (compressBlock name code) s (VG.Proof.Pbkdf2.X86_64.St P D W H s₀ v) := by
  have := VG.Proof.Pbkdf2.X86_64.so_le hz; have := VG.Proof.Pbkdf2.X86_64.N_le hz; have := VG.Proof.Pbkdf2.X86_64.B_le hz; have := hz.fits; have := hz.DN; have := hz.pad
  have := hz.NL
  exact VG.Proof.Pbkdf2.X86_64.cmp_ok hz hp hf h.toRegs fun s' h' r14 f _ =>
    ⟨h', r14.trans h.r14, (Memory.frame_bytesAt f (VG.Proof.Pbkdf2.X86_64.blk_disj hz hp (by omega)) (by omega)).trans h.pad⟩

theorem mid_st (hs : Shape H) (hR : H.Reloc) {s : State} (h : VG.Proof.Pbkdf2.X86_64.St P D W H s₀ v s) :
    WP isa (.block (Impl.Pbkdf2.X86_64.digest P D ++ loadKey P (P.N + P.B))) s (VG.Proof.Pbkdf2.X86_64.St P D W H s₀ v) := by
  have := VG.Proof.Pbkdf2.X86_64.so_le hz; have := VG.Proof.Pbkdf2.X86_64.N_le hz; have := VG.Proof.Pbkdf2.X86_64.B_le hz; have := hz.fits; have := hz.NL
  refine VG.Proof.Pbkdf2.X86_64.digest_ok hz hp hs h.toRegs h.pad fun s' g rd wr f _ p => ?_
  exact VG.Proof.Pbkdf2.X86_64.load_st hz hp hR (by omega)
    ⟨h.toRegs.write (fun r hr _ _ _ _ _ => g r hr) rd wr (VG.Proof.Pbkdf2.X86_64.frame_scr (a := P.so + 48 + P.N) (by omega) f),
      (g _ (by decide)).trans h.r14, p⟩

/-! ## Two runs -/

variable {s₀' : State} (hp' : VG.Proof.Pbkdf2.X86_64.Pre P D W s₀') (hq : VG.Proof.Pbkdf2.X86_64.PubEq s₀ s₀')
include hp' hq

theorem cmp_rel {name : String} {code : Prog isa} (hf : CalleeOk H code) (hc : VG.Proof.Pbkdf2.X86_64.Checks P D) :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.X86_64.St P D W H s₀ v s ∧ VG.Proof.Pbkdf2.X86_64.St P D W H s₀' v s') (compressBlock name code) fun s s' =>
      VG.Proof.Pbkdf2.X86_64.St P D W H s₀ v s ∧ VG.Proof.Pbkdf2.X86_64.St P D W H s₀' v s' := by
  obtain ⟨_, ha⟩ := hc.arg
  have su : RelCT isa (fun s s' => VG.Proof.Pbkdf2.X86_64.St P D W H s₀ v s ∧ VG.Proof.Pbkdf2.X86_64.St P D W H s₀' v s') (.block [.mov .rsi (.reg .rbp)])
      fun s s' => (VG.Proof.Pbkdf2.X86_64.St P D W H s₀ v s ∧ s.gpr .rsi = VG.Proof.Pbkdf2.X86_64.blk P s₀) ∧ (VG.Proof.Pbkdf2.X86_64.St P D W H s₀' v s' ∧ s'.gpr .rsi = VG.Proof.Pbkdf2.X86_64.blk P s₀') :=
    ((RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Pbkdf2.X86_64.regsS) (fun _ _ h => Taint.agree_ofRegs (St.agree hq h.1 h.2)) ha).wp
      fun _ _ h => ⟨wp_mov fun s₁ u₁ _ _ => WP.block_nil ⟨⟨h.1.toRegs.write
          (fun r _ _ _ hr _ _ => u₁.other r hr) u₁.rd u₁.wr (by rw [u₁.mem]; exact Frame.refl _ _),
          (u₁.other _ (by decide)).trans h.1.r14, by rw [u₁.mem]; exact h.1.pad⟩, by rw [u₁.gpr, h.1.rbp]⟩,
        wp_mov fun s₁ u₁ _ _ => WP.block_nil ⟨⟨h.2.toRegs.write
          (fun r _ _ _ hr _ _ => u₁.other r hr) u₁.rd u₁.wr (by rw [u₁.mem]; exact Frame.refl _ _),
          (u₁.other _ (by decide)).trans h.2.r14, by rw [u₁.mem]; exact h.2.pad⟩, by rw [u₁.gpr, h.2.rbp]⟩⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have call := compressAt_rel H hf (name := name)
    (P' := fun s s' => (VG.Proof.Pbkdf2.X86_64.St P D W H s₀ v s ∧ s.gpr .rsi = VG.Proof.Pbkdf2.X86_64.blk P s₀) ∧ (VG.Proof.Pbkdf2.X86_64.St P D W H s₀' v s' ∧ s'.gpr .rsi = VG.Proof.Pbkdf2.X86_64.blk P s₀'))
    fun s s' ⟨⟨h, hsi⟩, ⟨h', hsi'⟩⟩ => by
      have ag := St.agree hq h h'
      exact ⟨⟨_, _, _, VG.Proof.Pbkdf2.X86_64.callOk_of hz hp h.toRegs hsi⟩, ⟨_, _, _, VG.Proof.Pbkdf2.X86_64.callOk_of hz hp' h'.toRegs hsi'⟩,
        ag _ (by simp), ag _ (by simp), by rw [hsi, hsi', VG.Proof.Pbkdf2.X86_64.blk, VG.Proof.Pbkdf2.X86_64.blk, VG.Proof.Pbkdf2.X86_64.scr, VG.Proof.Pbkdf2.X86_64.scr, hq.r8], ag _ (by simp)⟩
  exact ((su.seq call).wp fun _ _ h => ⟨VG.Proof.Pbkdf2.X86_64.cmp_st hz hp hf h.1, VG.Proof.Pbkdf2.X86_64.cmp_st hz hp' hf h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem body_rel (hs : Shape H) (hR : H.Reloc) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hc : VG.Proof.Pbkdf2.X86_64.Checks P D) {r : Nat} :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀ (r + 1) s ∧ VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀' (r + 1) s') (body P D name code)
      fun s s' => (eval .ne s = some (r != 0) ∧ VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀ r s) ∧
        (eval .ne s' = some (r != 0) ∧ VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀' r s') := by
  have := VG.Proof.Pbkdf2.X86_64.so_le hz; have := VG.Proof.Pbkdf2.X86_64.N_le hz; have := VG.Proof.Pbkdf2.X86_64.B_le hz
  obtain ⟨_, hl⟩ := hc.load
  obtain ⟨_, hm⟩ := hc.mid
  obtain ⟨_, hfi⟩ := hc.fin
  have l0 : RelCT isa (fun s s' => VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀ (r + 1) s ∧ VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀' (r + 1) s') (.block (loadKey P 0))
      fun s s' => VG.Proof.Pbkdf2.X86_64.St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s ∧ VG.Proof.Pbkdf2.X86_64.St P D W H s₀' (BitVec.ofNat 64 (r + 1)) s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Pbkdf2.X86_64.regsS) (fun _ _ h =>
      Taint.agree_ofRegs (St.agree hq (St.of_inv h.1) (St.of_inv h.2))) hl).wp
      fun _ _ h => ⟨VG.Proof.Pbkdf2.X86_64.load_st hz hp hR (by omega) (St.of_inv h.1), VG.Proof.Pbkdf2.X86_64.load_st hz hp' hR (by omega) (St.of_inv h.2)⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have dl : RelCT isa (fun s s' => VG.Proof.Pbkdf2.X86_64.St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s ∧
        VG.Proof.Pbkdf2.X86_64.St P D W H s₀' (BitVec.ofNat 64 (r + 1)) s')
      (.block (Impl.Pbkdf2.X86_64.digest P D ++ loadKey P (P.N + P.B)))
      fun s s' => VG.Proof.Pbkdf2.X86_64.St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s ∧ VG.Proof.Pbkdf2.X86_64.St P D W H s₀' (BitVec.ofNat 64 (r + 1)) s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Pbkdf2.X86_64.regsS) (fun _ _ h => Taint.agree_ofRegs (St.agree hq h.1 h.2))
      hm).wp fun _ _ h => ⟨VG.Proof.Pbkdf2.X86_64.mid_st hz hp hs hR h.1, VG.Proof.Pbkdf2.X86_64.mid_st hz hp' hs hR h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have fin : RelCT isa (fun s s' => VG.Proof.Pbkdf2.X86_64.St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s ∧
        VG.Proof.Pbkdf2.X86_64.St P D W H s₀' (BitVec.ofNat 64 (r + 1)) s')
      (.block (Impl.Pbkdf2.X86_64.digest P D ++ (List.range (D / 4)).flatMap xorW ++ [.alu .sub .r14 (.imm 1)]))
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Pbkdf2.X86_64.regsS) (fun _ _ h => Taint.agree_ofRegs (St.agree hq h.1 h.2)) hfi
  have c := VG.Proof.Pbkdf2.X86_64.cmp_rel hz hp hp' hq (v := BitVec.ofNat 64 (r + 1)) hf hc (name := name)
  exact ((l0.seq (c.seq (dl.seq (c.seq fin)))).wp fun _ _ h =>
    ⟨VG.Proof.Pbkdf2.X86_64.body_ok hz hp hs hR hf h.1, VG.Proof.Pbkdf2.X86_64.body_ok hz hp' hs hR hf h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

theorem loop_rel (hs : Shape H) (hR : H.Reloc) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hc : VG.Proof.Pbkdf2.X86_64.Checks P D) {n : Nat} :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀ (n + 1) s ∧ VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀' (n + 1) s') (.loop (body P D name code) .ne)
      fun _ _ => True :=
  RelCT.loop (M := isa) (body := body P D name code) (c := .ne) (Q := fun _ _ => True)
    (fun m s s' => VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀ (m + 1) s ∧ VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀' (m + 1) s') (fun m => by
      intro s s' t t' u u' h e e'
      obtain ⟨ht, ⟨z, i⟩, ⟨z', i'⟩⟩ := VG.Proof.Pbkdf2.X86_64.body_rel hz hp hp' hq hs hR hf hc _ _ _ _ _ _ h e e'
      refine ⟨ht, z.trans z'.symm, fun _ => trivial, fun hc' => ?_⟩
      have hc'' : some (m != 0) = some true := z.symm.trans hc'
      cases m with
      | zero => cases hc''
      | succ m => exact ⟨m, by omega, i, i'⟩) n

theorem iterate_rel {S : StreamingHash} {iv : H.HV} (ho : VG.Proof.Pbkdf2.X86_64.HashOk P D W S H iv) {name : String}
    {code : Prog isa} (hf : CalleeOk H code) (hc : VG.Proof.Pbkdf2.X86_64.Checks P D) :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (iterate P D name code) fun _ _ => True := by
  obtain ⟨_, hpr⟩ := hc.pro
  obtain ⟨_, hep⟩ := hc.epi
  obtain ⟨_, hit⟩ := hc.ite
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block (prologue P D)) fun s s' =>
      (VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀ (VG.Proof.Pbkdf2.X86_64.nn s₀) s ∧ s.zf = some (decide (VG.Proof.Pbkdf2.X86_64.nn s₀ = 0))) ∧
      (VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀' (VG.Proof.Pbkdf2.X86_64.nn s₀') s' ∧ s'.zf = some (decide (VG.Proof.Pbkdf2.X86_64.nn s₀' = 0))) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rcx, .r8, .rsp])
      (P := fun s s' => s = s₀ ∧ s' = s₀') (fun _ _ ⟨e, e'⟩ => Taint.agree_ofRegs fun r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) hpr).wp
      fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨VG.Proof.Pbkdf2.X86_64.prologue_ok hz hp ho.shape ho.lenOk, VG.Proof.Pbkdf2.X86_64.prologue_ok hz hp' ho.shape ho.lenOk⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have br : RelCT isa (fun s s' =>
        (VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀ (VG.Proof.Pbkdf2.X86_64.nn s₀) s ∧ s.zf = some (decide (VG.Proof.Pbkdf2.X86_64.nn s₀ = 0))) ∧
        (VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀' (VG.Proof.Pbkdf2.X86_64.nn s₀') s' ∧ s'.zf = some (decide (VG.Proof.Pbkdf2.X86_64.nn s₀' = 0))))
      (.ite .e (.block []) (.loop (body P D name code) .ne))
      fun s s' => VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀ 0 s ∧ VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀' 0 s' := by
    refine (RelCT.ite (fun s s' h => ?_) (RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ _ => Taint.agree_ofRegs (by simp)) hit) ?_).wp
      (fun _ _ h => ⟨VG.Proof.Pbkdf2.X86_64.loop_ok hz hp ho.shape ho.reloc hf h.1.1 h.1.2,
        VG.Proof.Pbkdf2.X86_64.loop_ok hz hp' ho.shape ho.reloc hf h.2.1 h.2.2⟩) |>.mono (fun _ _ h => h) fun _ _ h => h.2
    · show s.zf = s'.zf
      rw [h.1.2, h.2.2, hq.nn]
    · intro s s' t t' u u' ⟨⟨⟨i, z⟩, ⟨i', _⟩⟩, hc'⟩ e e'
      have hc'' : some (decide (VG.Proof.Pbkdf2.X86_64.nn s₀ = 0)) = some false := z.symm.trans hc'
      have hne : VG.Proof.Pbkdf2.X86_64.nn s₀ ≠ 0 := fun h0 => by rw [h0] at hc''; cases hc''
      obtain ⟨m, hm⟩ : ∃ m, VG.Proof.Pbkdf2.X86_64.nn s₀ = m + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero hne).symm⟩
      rw [hm] at i
      rw [← hq.nn, hm] at i'
      exact VG.Proof.Pbkdf2.X86_64.loop_rel hz hp hp' hq ho.shape ho.reloc hf hc _ _ _ _ _ _ ⟨i, i'⟩ e e'
  have epi : RelCT isa (fun s s' => VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀ 0 s ∧ VG.Proof.Pbkdf2.X86_64.Inv P D W H s₀' 0 s') (.block (restore P))
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r15]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.r15, h.2.r15, VG.Proof.Pbkdf2.X86_64.scr, VG.Proof.Pbkdf2.X86_64.scr, hq.r8]) hep
  exact pro.seq (br.seq epi)

end

/-! ## Verified -/

theorem pubEq_of {S : StreamingHash} {W : Nat} {s₁ s₂ : State} (h : (VG.Proof.Pbkdf2.X86_64.iterK S W).pub s₁ s₂) : VG.Proof.Pbkdf2.X86_64.PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- `iterate` is verified against `iterK`, for any hash function the proof
supports (`HashOk`), whose pieces of code the taint analysis accepts
(`Checks`), and any compression function (`CalleeOk`), if it never loads
MXCSR. -/
theorem verified {P : Params} {D W : Nat} {S : StreamingHash} {H : Md P.B P.N P.L} {iv : H.HV}
    (ho : VG.Proof.Pbkdf2.X86_64.HashOk P D W S H iv) (hc : VG.Proof.Pbkdf2.X86_64.Checks P D) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hm : (iterate P D name code).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsat : ∃ s, (VG.Proof.Pbkdf2.X86_64.iterK S W).pre s) :
    Verified X86_64.target (iterate P D name code) (VG.Proof.Pbkdf2.X86_64.iterK S W) := by
  refine ⟨VG.Proof.Pbkdf2.X86_64.iterate_ok ho hf hm, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  exact (VG.Proof.Pbkdf2.X86_64.iterate_rel ho.sizes (VG.Proof.Pbkdf2.X86_64.pre_of ho.link.hS ho.link.hD h₁) (VG.Proof.Pbkdf2.X86_64.pre_of ho.link.hS ho.link.hD h₂)
    (VG.Proof.Pbkdf2.X86_64.pubEq_of hpub) ho hf hc _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- `iterK` implies the shared contract, for any hash function and scratch
space, given that the shared contract is satisfiable. -/
theorem iterImp (S : StreamingHash) (W : Nat) (h : ∃ s, (Spec.Pbkdf2.iterateContract S W X86_64.abi 8).pre s) :
    (VG.Proof.Pbkdf2.X86_64.iterK S W).Implies (Spec.Pbkdf2.iterateContract S W X86_64.abi 8) := by
  generic_implies [
    Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, VG.Proof.Pbkdf2.X86_64.iterK, X86_64.abi, X86_64.argRegs] using h

/-- A state satisfying `iterate`'s precondition, with states of `S` bytes, a
digest of `D` bytes and `8 W` bytes of scratch space. -/
def iterSat (S D W : Nat) : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rsi => 0x20000 | .rcx => 0x30000 | .r8 => 0x40000
    | .rsp => 0x90000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x10000, 2 * S⟩, ⟨0x20000, D⟩]
  wr := [⟨0x30000, D⟩, ⟨0x40000, 8 * W⟩]

end VG.Proof.Pbkdf2.X86_64

end
