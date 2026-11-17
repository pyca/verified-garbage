module

public import VerifiedGarbage.Proof.Dsa.RandomBytes
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Dsa.RandomSignRemaining
public import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Proof.Dsa.SignContractWith
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Impl.Dsa.Arm.Random
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Dsa.Arm.RandomFrame`, which this module and modules that import it used -/

section

/-! ### `Dsa.Arm.RandomABI`, which only this module used -/

section

/-!
# The randomized signer's resources on 32-bit ARM, from the shared contract

`vg_dsa_sign_random(out, out_len, used, key, key_len, p_len, q_len, digest,
digest_len, rand, rand_len, scratch, scratch_len)` has its first four
arguments in `r0`–`r3` and the others on the stack (AAPCS). The 144 bytes
of stack below `sp` hold its frame (112 bytes) and, below it, the stack
arguments it pushes for the supplied-nonce signer (32 bytes).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm

section
variable (s : State)

/-- The caller's buffers, and its stack arguments. -/
abbrev rOut : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
abbrev rUsed : Region := ⟨State.addr (s.gpr .r2), 8⟩
abbrev rKeyR : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
abbrev rDigestR : Region := ⟨State.addr (stackArg s 3), (stackArg s 4).toNat⟩
abbrev rRandR : Region := ⟨State.addr (stackArg s 5), (stackArg s 6).toNat⟩
abbrev rScratch : Region := ⟨State.addr (stackArg s 7), (stackArg s 8).toNat * 8⟩
abbrev rArgs : Region := ⟨State.addr s.sp, 36⟩

/-- The lowest byte of the stack the signer uses, 144 bytes below `sp`. -/
abbrev rLow : Addr := State.addr s.sp - 144#64

abbrev rStack : Region := ⟨rLow s, 144⟩

end

structure RandomABI (s : State) : Prop where
  stackLow : 144 ≤ s.sp.toNat
  stackBound : s.sp.toNat + 36 ≤ 2 ^ 32
  rd : s.rd = [rKeyR s, rDigestR s, rRandR s, rArgs s]
  wr : s.wr = [rOut s, rUsed s, rScratch s]
  outUsed : (rOut s).Disjoint (rUsed s)
  outKey : (rOut s).Disjoint (rKeyR s)
  outDigest : (rOut s).Disjoint (rDigestR s)
  outRand : (rOut s).Disjoint (rRandR s)
  outScratch : (rOut s).Disjoint (rScratch s)
  outArgs : (rOut s).Disjoint (rArgs s)
  usedKey : (rUsed s).Disjoint (rKeyR s)
  usedDigest : (rUsed s).Disjoint (rDigestR s)
  usedRand : (rUsed s).Disjoint (rRandR s)
  usedScratch : (rUsed s).Disjoint (rScratch s)
  usedArgs : (rUsed s).Disjoint (rArgs s)
  keyScratch : (rKeyR s).Disjoint (rScratch s)
  digestScratch : (rDigestR s).Disjoint (rScratch s)
  randScratch : (rRandR s).Disjoint (rScratch s)
  scratchArgs : (rScratch s).Disjoint (rArgs s)
  stackOut : (rStack s).Disjoint (rOut s)
  stackUsed : (rStack s).Disjoint (rUsed s)
  stackKey : (rStack s).Disjoint (rKeyR s)
  stackDigest : (rStack s).Disjoint (rDigestR s)
  stackRand : (rStack s).Disjoint (rRandR s)
  stackScratch : (rStack s).Disjoint (rScratch s)
  stackArgs : (rStack s).Disjoint (rArgs s)
  outBound : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  usedBound : (s.gpr .r2).toNat + 8 ≤ 2 ^ 32
  keyBound : (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32
  digestBound : (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 32
  randBound : (stackArg s 5).toNat + (stackArg s 6).toNat ≤ 2 ^ 32
  scratchBound : (stackArg s 7).toNat + (stackArg s 8).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Dsa.lengthsValid (stackArg s 1).toNat (stackArg s 2).toNat
  outLength : (s.gpr .r1).toNat = 2 * (stackArg s 2).toNat
  keyLength : (stackArg s 0).toNat = 3 * (stackArg s 1).toNat + 2 * (stackArg s 2).toNat
  scratchLength : Spec.Dsa.randomSignScratchWords (stackArg s 1).toNat ≤ (stackArg s 8).toNat

theorem randomABI_of {s : State} (h : (randomSignCheckedContract Arm.abi 144).pre s) : RandomABI s := by
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.stackArgAddr, BitVec.add_zero] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36⟩

/-! ## What the specification reads -/

/-- The inputs of the specification. -/
def rInput (s₀ : State) : VG.Proof.Dsa.RandomSignInput where
  pLen := (stackArg s₀ 1).toNat
  qLen := (stackArg s₀ 2).toNat
  key := Spec.Rsa.bytesAt s₀.mem (State.addr (s₀.gpr .r3)) (stackArg s₀ 0).toNat
  digest := Spec.Rsa.bytesAt s₀.mem (State.addr (stackArg s₀ 3)) (stackArg s₀ 4).toNat
  rand := Spec.Rsa.bytesAt s₀.mem (State.addr (stackArg s₀ 5)) (stackArg s₀ 6).toNat

/-- The specification's result. -/
abbrev rResult (s₀ : State) : Spec.Dsa.RandomSignResult :=
  Spec.Dsa.randomSignBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key (rInput s₀).digest (rInput s₀).rand

/-- The public key bytes of the entry. -/
abbrev keyLeak (s₀ : State) : List Nat :=
  Spec.Dsa.publicBytesLeak (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key

/-- q's bytes, and their address. -/
def rQBytes (s₀ : State) : List Byte := ((rInput s₀).key.drop (rInput s₀).pLen).take (rInput s₀).qLen
def rQ (s₀ : State) : BitVec 32 := s₀.gpr .r3 + stackArg s₀ 1

/-- q's significant bytes, and the first of them. -/
abbrev rWidth (s₀ : State) : Nat := (VG.Proof.Dsa.significant (rQBytes s₀)).1
abbrev rLead (s₀ : State) : Byte := (VG.Proof.Dsa.significant (rQBytes s₀)).2

/-- q, as the specification reads it. -/
abbrev rq (s₀ : State) : Nat := Spec.Dsa.decodeBE (rQBytes s₀)

theorem rQ_decode (s₀ : State) :
    rq s₀ = (Spec.Dsa.privateKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key).params.q := rfl

theorem rBytes_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

theorem rQBytes_length {s₀ : State} (A : RandomABI s₀) : (rQBytes s₀).length = (stackArg s₀ 2).toNat := by
  simp only [rQBytes, rInput, List.length_take, List.length_drop, rBytes_length, A.keyLength]
  omega_using []

theorem rQBytes_le {s₀ : State} (A : RandomABI s₀) : (rQBytes s₀).length ≤ 32 := by
  rw [rQBytes_length A]; have := A.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]

theorem rQBytes_pos {s₀ : State} (A : RandomABI s₀) : 0 < (rQBytes s₀).length := by
  rw [rQBytes_length A]; have := A.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]

theorem rWidth_le (s₀ : State) : rWidth s₀ ≤ (rQBytes s₀).length :=
  VG.Proof.Dsa.significant_fits _

end VG.Proof.Dsa.Arm

end

end


/-!
# The randomized signer's frame on 32-bit ARM

`r11` holds the frame's base `B` (`RF`): its `frameBytes` bytes are writable
and the caller's stack arguments above them readable, all below `2³²`.
Slots and arguments are 32-bit words at offsets from `B` (`slot`). From
the entry state `s₀`, the frame lies 32 bytes above the lowest byte of stack
the signer uses (`rBase`), and the body writes only that stack, `out`,
`scratch` and `used` (`rWrites`), so it reads the caller's arguments and
input bytes as they were on entry (`RReady`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_ldr wp_str wp_ldrb wp_strb)

/-- The frame and the arguments above it. -/
structure RF (s : State) (B : Addr) : Prop where
  base : State.addr (s.gpr .r11) = B
  wr : (⟨B, frameBytes⟩ : Region) ∈ s.wr
  args : (⟨off B frameBytes, 36⟩ : Region) ∈ s.rd
  nowrap : B.toNat + frameBytes + 36 ≤ 2 ^ 32

theorem RF.toNat {s : State} {B : Addr} (h : RF s B) : (s.gpr .r11).toNat = B.toNat := by
  rw [← h.base, VG.Proof.X25519.Arm.addr_toNat]

/-- `[r11 + d]`. -/
theorem RF.ea {s : State} {B : Addr} (h : RF s B) {d : Nat} (hd : d < frameBytes + 36) :
    State.addr (s.gpr .r11 + BitVec.ofNat 32 d) = off B d := by
  rw [VG.Arm.addr_add (by have := h.nowrap; have := h.toNat; omega_arith), h.base]

theorem RF.read {s : State} {B : Addr} (h : RF s B) {d n : Nat} (hd : d + n ≤ frameBytes) :
    InRegions (s.rd ++ s.wr) (off B d) n :=
  ⟨_, List.mem_append_right _ h.wr, Offset.contains_base B hd (by have := h.nowrap; unfold frameBytes at *; omega_using [hd])⟩

theorem RF.write {s : State} {B : Addr} (h : RF s B) {d n : Nat} (hd : d + n ≤ frameBytes) :
    InRegions s.wr (off B d) n :=
  ⟨_, h.wr, Offset.contains_base B hd (by have := h.nowrap; unfold frameBytes at *; omega_using [hd])⟩

theorem RF.readArg {s : State} {B : Addr} (h : RF s B) {j : Nat} (hj : j < 9) :
    InRegions (s.rd ++ s.wr) (off B (Random.arg j)) 4 := by
  refine ⟨_, List.mem_append_left _ h.args, ?_⟩
  have e : off B (Random.arg j) = off B frameBytes + BitVec.ofNat 64 (4 * j) := by
    rw [off, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl
  rw [e]
  exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

theorem RF.of_rest {ws : List Reg} {s s' : State} {B : Addr} (h : RF s B) (R : Rest ws s s')
    (h11 : .r11 ∉ ws) : RF s' B :=
  ⟨by rw [R.gpr _ h11]; exact h.base, R.wr ▸ h.wr, R.rd ▸ h.args, h.nowrap⟩

/-- The 32-bit word at offset `d` of `B`. -/
abbrev slot (m : Mem) (B : Addr) (d : Nat) : BitVec 32 := m.readW (off B d) 32

theorem slot_write_self (m : Mem) (B : Addr) (d : Nat) (v : BitVec 32) :
    slot (m.writeW (off B d) v) B d = v := Mem.readW_writeW_self32 _ _ _

theorem slot_write_ne (m : Mem) (B : Addr) {o d : Nat} {w : Nat} (v : BitVec w)
    (hsep : d + 4 ≤ o ∨ o + w / 8 ≤ d) (hd : d + 4 ≤ 2 ^ 64) (ho : o + w / 8 ≤ 2 ^ 64) :
    slot (m.writeW (off B o) v) B d = slot m B d :=
  Mem.readW_writeW_sep (Offset.sep B hsep hd ho) (by decide)

/-! ## Where things are -/

/-- The frame's base. -/
abbrev rBase (s₀ : State) : Addr := off (rLow s₀) 32

/-- Where the body may write. -/
def rWrites (s₀ : State) : List Region := [rStack s₀, rOut s₀, rScratch s₀, rUsed s₀]

theorem rBase_off (s₀ : State) (d : Nat) : off (rBase s₀) d = off (rLow s₀) (32 + d) := by
  simp only [rBase, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {s₀ : State} (A : RandomABI s₀)
include A

theorem rLow_toNat : (rLow s₀).toNat = s₀.sp.toNat - 144 := by
  have := A.stackLow
  rw [rLow, BitVec.toNat_sub, VG.Proof.X25519.Arm.addr_toNat, show (144#64).toNat = 144 from rfl]
  have := s₀.sp.isLt
  omega_arith

theorem off_rLow_toNat {d : Nat} (hd : d ≤ 180) : (off (rLow s₀) d).toNat = (rLow s₀).toNat + d := by
  have := A.stackBound
  have := rLow_toNat A
  rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [hd]),
    Nat.mod_eq_of_lt (by omega_using [hd, this])]

theorem rBase_toNat : (rBase s₀).toNat = s₀.sp.toNat - 112 := by
  rw [rBase, off_rLow_toNat A (by decide), rLow_toNat A]; have := A.stackLow; omega_using [this]

/-- The caller's stack argument `j`. -/
theorem rBase_arg {j : Nat} (hj : j < 9) : off (rBase s₀) (Random.arg j) = stackArgAddr s₀ j := by
  apply BitVec.eq_of_toNat_eq
  have := A.stackBound
  have := A.stackLow
  rw [rBase_off, off_rLow_toNat A (by unfold Random.arg frameBytes; omega_using [hj]), rLow_toNat A, stackArgAddr,
    VG.Proof.X25519.Arm.addr_toNat, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * j) (by omega_using [hj]),
    Nat.mod_eq_of_lt (by omega_arith)]
  unfold Random.arg frameBytes; omega_using [this]

theorem rBase_args : off (rBase s₀) frameBytes = State.addr s₀.sp := by
  have := rBase_arg A (j := 0) (by decide)
  rwa [stackArgAddr, Nat.mul_zero, BitVec.add_zero] at this

/-- The frame reserved on entry. -/
theorem alloc_base : State.addr (s₀.sp - BitVec.ofNat 32 frameBytes) = rBase s₀ := by
  apply BitVec.eq_of_toNat_eq
  have := A.stackLow
  rw [rBase_toNat A, VG.Proof.X25519.Arm.addr_toNat, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := s₀.sp.isLt
  unfold frameBytes; omega_arith

/-- The arguments' 36 bytes are apart from where the body writes. -/
theorem rArgs_apart : ∀ r ∈ rWrites s₀, Region.Disjoint (rArgs s₀) r := by
  intro r hr
  simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact A.stackArgs.symm
  · exact A.outArgs.symm
  · exact A.scratchArgs.symm
  · exact A.usedArgs.symm
end

/-! ## The state the body keeps -/

/-- The frame, the permissions of the entry state with the frame, and memory
changed only where the body may write. -/
structure RReady (s₀ t : State) : Prop where
  rf : RF t (rBase s₀)
  sp : t.sp = s₀.sp - BitVec.ofNat 32 frameBytes
  rd : t.rd = s₀.rd
  wr : t.wr = ⟨rBase s₀, frameBytes⟩ :: s₀.wr
  frame : Frame (rWrites s₀) s₀.mem t.mem

/-- Registers but `r11` and memory within the stack change. -/
theorem RReady.congr {s₀ t t' : State} {ws : List Reg} (h : RReady s₀ t) (R : Rest ws t t')
    (hm : Frame [rStack s₀] t.mem t'.mem) (h11 : .r11 ∉ ws := by decide) : RReady s₀ t' :=
  ⟨h.rf.of_rest R h11, R.sp.trans h.sp, R.rd.trans h.rd, R.wr.trans h.wr,
    h.frame.trans (hm.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [rWrites])⟩

theorem RReady.upd {s₀ t t' : State} {d : Reg} {v : BitVec 32} (h : RReady s₀ t) (u : Upd t t' d v)
    (hd : d ≠ .r11 := by decide) : RReady s₀ t' :=
  h.congr (ws := [d]) (u.rest (List.mem_singleton_self _)) (by rw [u.mem]; exact Frame.refl _ _)
    (by simpa using hd.symm)

theorem RReady.fupd {s₀ t t' : State} (h : RReady s₀ t) (u : Fupd t t') : RReady s₀ t' :=
  h.congr (ws := []) (u.rest _) (by rw [u.mem]; exact Frame.refl _ _)

/-- A store to the frame. -/
theorem frame_store (s₀ : State) (m : Mem) {d : Nat} {w : Nat} (hd : d + w / 8 ≤ frameBytes)
    (v : BitVec w) : Frame [rStack s₀] m (m.writeW (off (rBase s₀) d) v) := by
  refine Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) v ?_
  rw [rBase_off]
  exact Offset.contains_base _ (by unfold frameBytes at hd; omega_using [hd]) (by unfold frameBytes at hd; omega_using [hd])

theorem RReady.mupd {s₀ t t' : State} {d w : Nat} {v : BitVec w} (h : RReady s₀ t)
    (u : Mupd t t' (t.mem.writeW (off (rBase s₀) d) v)) (hd : d + w / 8 ≤ frameBytes) : RReady s₀ t' :=
  h.congr (ws := []) (u.rest _) (by rw [u.mem]; exact frame_store s₀ _ hd v)

/-- The caller's stack arguments. -/
theorem RReady.arg {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t) {j : Nat} (hj : j < 9) :
    slot t.mem (rBase s₀) (Random.arg j) = stackArg s₀ j := by
  rw [slot, rBase_arg A hj, stackArg]
  refine h.frame.readW (r := rArgs s₀) ?_ (rArgs_apart A) (by decide)
  rw [stackArgAddr, VG.Arm.addr_add (by have := A.stackBound; omega_using [hj, this])]
  exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

/-! ## Slots apart from what changed -/

theorem store_in (B : Addr) (m : Mem) {d o n : Nat} (v : BitVec 32) {rs : List (Nat × Nat)}
    (hm : (o, n) ∈ rs) (h₁ : o ≤ d) (h₂ : d + 4 ≤ o + n) (hb : d + 4 ≤ 2 ^ 64 := by omega) :
    Outs B rs m (m.writeW (off B d) v) :=
  Outs.of_outside ((writeW32_outside m B v hb).mono h₁ h₂) hm

theorem store_outs (B : Addr) (m : Mem) {d : Nat} (v : BitVec 32) {rs : List (Nat × Nat)}
    (hd : (d, 4) ∈ rs) (hb : d + 4 ≤ 2 ^ 64 := by decide) : Outs B rs m (m.writeW (off B d) v) :=
  Outs.of_outside (writeW32_outside m B v hb) hd

theorem slot_outs {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 4 < 2 ^ 64 := by decide) :
    slot m' B d = slot m B d :=
  Mem.readW_congr fun i hi => h _ fun r hr => by
    have := hd r hr
    have hi' : i < 4 := hi
    rw [ofs_off B (show d + i < 2 ^ 64 by omega_using [hd', hi])]; omega_using [hi, this]

/-! ## Loads and stores of the frame -/

section
variable {s₀ t : State} {is : List Instr} {Q : State → Prop}

/-- `ldr r, [r11, #d]`, a slot of the frame. -/
theorem wp_ld (h : RReady s₀ t) {r : Reg} {d : Nat} (hd : d + 4 ≤ frameBytes)
    (k : ∀ u, Upd t u r (slot t.mem (rBase s₀) d) → WP isa (.block is) u Q) :
    WP isa (.block (ld r d :: is)) t Q :=
  wp_ldr (by unfold frameBytes at hd; omega_using [hd]) (h.rf.ea (by omega_using [hd])) (h.rf.read hd) k

/-- `ldr r, [r11, #arg j]`, the caller's stack argument `j`. -/
theorem wp_ldArg (A : RandomABI s₀) (h : RReady s₀ t) {r : Reg} {j : Nat} (hj : j < 9)
    (k : ∀ u, Upd t u r (stackArg s₀ j) → WP isa (.block is) u Q) :
    WP isa (.block (ld r (Random.arg j) :: is)) t Q :=
  wp_ldr (by unfold Random.arg frameBytes; omega_using [hj]) (h.rf.ea (by unfold Random.arg; omega_using [hj])) (h.rf.readArg hj)
    fun u v => k u (by rw [← h.arg A hj]; exact v)

/-- `str r, [r11, #d]`, a slot of the frame. -/
theorem wp_st (h : RReady s₀ t) {r : Reg} {d : Nat} (hd : d + 4 ≤ frameBytes)
    (k : ∀ u, Mupd t u (t.mem.writeW (off (rBase s₀) d) (t.gpr r)) → RReady s₀ u → WP isa (.block is) u Q) :
    WP isa (.block (st r d :: is)) t Q :=
  wp_str (by unfold frameBytes at hd; omega_using [hd]) (h.rf.ea (by omega_using [hd])) (h.rf.write hd) fun u v => k u v (h.mupd v hd)

/-- `str r, [r11, #d]`, keeping the flags. -/
theorem wp_stF (h : RReady s₀ t) {r : Reg} {d : Nat} (hd : d + 4 ≤ frameBytes)
    (k : ∀ u, Mupd t u (t.mem.writeW (off (rBase s₀) d) (t.gpr r)) → RReady s₀ u → u.z = t.z → u.c = t.c →
      WP isa (.block is) u Q) :
    WP isa (.block (st r d :: is)) t Q := by
  have e := h.rf.ea (d := d) (by omega_using [hd])
  refine VG.Proof.X25519.Arm.WP.cons (exec_str (by unfold frameBytes at hd; omega_using [hd]) (by rw [e]; exact h.rf.write hd)) ?_
  rw [e]
  exact k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ (h.mupd ⟨rfl, rfl, rfl, rfl, rfl⟩ hd) rfl rfl

end

/-! ## Bytes of the caller's buffers -/

/-- `bs` at `p`: readable bytes below `2³²`. -/
structure BytesIn (s : State) (p : BitVec 32) (bs : List Byte) : Prop where
  fit : p.toNat + bs.length ≤ 2 ^ 32
  rd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1
  val : ∀ i (h : i < bs.length), s.mem (State.addr p + BitVec.ofNat 64 i) = bs[i]

theorem BytesIn.drop {s : State} {p : BitVec 32} {bs : List Byte} (h : BytesIn s p bs) (j : Nat)
    (hj : j ≤ bs.length) : BytesIn s (p + BitVec.ofNat 32 j) (bs.drop j) := by
  have hfit := h.fit
  have e : ∀ i, j + i < bs.length → State.addr (p + BitVec.ofNat 32 j) + BitVec.ofNat 64 i =
      State.addr p + BitVec.ofNat 64 (j + i) := fun i hi => by
    rw [VG.Arm.addr_add (by omega_using [hfit, hi]), Offset.add_add]
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [List.length_drop]
    by_cases hjl : j = bs.length
    · rw [hjl, Nat.sub_self, Nat.add_zero]; exact Nat.le_of_lt (BitVec.isLt _)
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega_using [hj, hfit, hjl]),
        Nat.mod_eq_of_lt (by omega_using [hj, hfit, hjl])]; omega_using [hj, hfit]
  · rw [List.length_drop] at hi
    rw [e i (by omega_using [hi])]; exact h.rd _ (by omega_using [hi])
  · rw [List.length_drop] at hi
    rw [e i (by omega_using [hi]), h.val _ (by omega_using [hi]), List.getElem_drop]

theorem BytesIn.take {s : State} {p : BitVec 32} {bs : List Byte} (h : BytesIn s p bs) (n : Nat) :
    BytesIn s p (bs.take n) := by
  refine ⟨by rw [List.length_take]; have := h.fit; omega_using [this], fun i hi => ?_, fun i hi => ?_⟩
  · rw [List.length_take] at hi; exact h.rd i (by omega_using [hi])
  · rw [List.length_take] at hi; rw [List.getElem_take]; exact h.val i (by omega_using [hi])

theorem BytesIn.congr {s t : State} {p : BitVec 32} {bs : List Byte} (h : BytesIn s p bs)
    (hm : t.mem = s.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr) : BytesIn t p bs :=
  ⟨h.fit, fun i hi => by rw [hr, hw]; exact h.rd i hi, fun i hi => by rw [hm]; exact h.val i hi⟩

/-- Bytes the body reads, apart from where it writes. -/
theorem RReady.bytes {s₀ t : State} (h : RReady s₀ t) {p : BitVec 32} {n : Nat}
    (hr : (⟨State.addr p, n⟩ : Region) ∈ s₀.rd) (hfit : p.toNat + n ≤ 2 ^ 32)
    (hd : ∀ r ∈ rWrites s₀, Region.Disjoint ⟨State.addr p, n⟩ r) :
    BytesIn t p (Spec.Rsa.bytesAt s₀.mem (State.addr p) n) := by
  refine ⟨by rw [rBytes_length]; exact hfit, fun i hi => ?_, fun i hi => ?_⟩
  · rw [rBytes_length] at hi
    exact ⟨_, List.mem_append_left _ (h.rd ▸ hr), Offset.contains_base _ (by omega_using [hi]) (by omega_using [hfit, hi])⟩
  · rw [rBytes_length] at hi
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    exact h.frame.bytes (R := ⟨State.addr p, n⟩) hd (show n ≤ 2 ^ 64 by omega_using [hfit]) hi

theorem RReady.rand {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t) :
    BytesIn t (stackArg s₀ 5) (rInput s₀).rand := by
  refine h.bytes (by rw [A.rd]; simp) A.randBound fun r hr => ?_
  simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact A.stackRand.symm
  · exact A.outRand.symm
  · exact A.randScratch
  · exact A.usedRand.symm

theorem RReady.key {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t) :
    BytesIn t (s₀.gpr .r3) (rInput s₀).key := by
  refine h.bytes (by rw [A.rd]; simp) A.keyBound fun r hr => ?_
  simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact A.stackKey.symm
  · exact A.outKey.symm
  · exact A.keyScratch
  · exact A.usedKey.symm

theorem RReady.q {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t) : BytesIn t (rQ s₀) (rQBytes s₀) := by
  have hk := h.key A
  have hp : (stackArg s₀ 1).toNat ≤ (rInput s₀).key.length := by
    simp only [rInput, rBytes_length, A.keyLength]; omega_using []
  have := (hk.drop _ hp).take (rInput s₀).qLen
  simpa only [rQ, rQBytes, rInput, BitVec.ofNat_toNat, BitVec.setWidth_eq] using this

end VG.Proof.Dsa.Arm

end

end

/-!
# Scanning the public q for its significant bytes (32-bit ARM)

`significant` reads the `q_len` bytes of q from its first, keeping the
count of bytes from the first nonzero one (`r3`) and that byte (`r4`):
`VG.Proof.Dsa.significant`. Its branches are on q's bytes, which are public.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp wp_subs wp_ldrb op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero)
open VG.Proof.Dsa (scanNext scanFinish scanFinish_step scanFinish_nil)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `cmp n, #0`. -/
theorem wp_cmp0 {n : Reg} (k : ∀ s', Fupd s s' → s'.z = (s.gpr n == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.cmp n (.imm 0) :: is)) s Q :=
  wp_cmp (op2_imm (by decide)) fun s' f z => k s' f (by rw [z]; exact congrArg (· == 0) (BitVec.sub_zero _))

/-- `subs d, d, #1`. -/
theorem wp_dec {d : Reg} (k : ∀ s', Upd s s' d (s.gpr d - 1) → s'.z = (s.gpr d - 1 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d d (.imm 1) :: is)) s Q :=
  wp_subs (op2_imm (by decide)) k

/-- `add d, d, #1`. -/
theorem wp_inc {d : Reg} (k : ∀ s', Upd s s' d (s.gpr d + 1) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .add d d (.imm 1) :: is)) s Q :=
  wp_dp (op2_imm (by decide)) k

end

theorem ofNat_sub_one {k : Nat} (hk : 1 ≤ k) : BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [show (1 : BitVec 32).toNat = 1 from rfl]
  omega_using [hk]

theorem byte_beq_zero (b : Byte) : (b.setWidth 32 == 0) = decide (b = 0) := by
  by_cases hb0 : b = 0
  · subst hb0; rfl
  · simp only [hb0, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e; apply hb0; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat e
    rw [VG.Proof.Dsa.toNat_setWidth8] at this
    rw [this]; rfl

/-- The scan's state, with `rest` to read. -/
structure ScanState (s : State) (p : BitVec 32) (rest : List Byte) (found : Nat × Byte) : Prop where
  r1 : s.gpr .r1 = p
  r2 : s.gpr .r2 = BitVec.ofNat 32 rest.length
  r3 : s.gpr .r3 = BitVec.ofNat 32 found.1
  r4 : s.gpr .r4 = found.2.setWidth 32
  bytes : BytesIn s p rest
  bound : found.1 < 2 ^ 32
  zero : found.1 = 0 → found.2 = 0

abbrev scanRegs : List Reg := [.r0, .r1, .r2, .r3, .r4]

theorem significantByte_ok {s : State} {p : BitVec 32} {b : Byte} {rest : List Byte} {found : Nat × Byte}
    (h : ScanState s p (b :: rest) found) (hl : rest.length + 1 < 2 ^ 32) :
    WP isa significantByte s fun t =>
      ScanState t (p + 1) rest (scanNext found (rest.length + 1) b) ∧
      t.z = decide (rest.length = 0) ∧ t.mem = s.mem ∧ Rest scanRegs s t := by
  have hb : s.mem (State.addr p) = b := by
    have := h.bytes.val 0 (by simp)
    simpa only [BitVec.add_zero, List.getElem_cons_zero] using this
  have hr : InRegions (s.rd ++ s.wr) (State.addr p) 1 := by
    simpa only [BitVec.add_zero] using h.bytes.rd 0 (by simp)
  unfold significantByte significantChoose
  refine WP.seq (wp_ldrb (by decide) (by rw [BitVec.add_zero, h.r1]) hr fun s₁ u₁ => WP.block_nil ?_)
  rw [hb] at u₁
  -- The choice, then the step.
  have after : ∀ (u : State), u.gpr .r3 = BitVec.ofNat 32 (scanNext found (rest.length + 1) b).1 →
      u.gpr .r4 = (scanNext found (rest.length + 1) b).2.setWidth 32 → u.mem = s.mem →
      Rest scanRegs s u → u.gpr .r1 = p → u.gpr .r2 = BitVec.ofNat 32 (rest.length + 1) →
      WP isa (.block [.dp .add .r1 .r1 (.imm 1), .subs .r2 .r2 (.imm 1)]) u fun t =>
        ScanState t (p + 1) rest (scanNext found (rest.length + 1) b) ∧
        t.z = decide (rest.length = 0) ∧ t.mem = s.mem ∧ Rest scanRegs s t := by
    intro u h3 h4 hm R e1 e2
    refine wp_inc fun s₂ u₂ => wp_dec fun s₃ u₃ z₃ => WP.block_nil ?_
    have R₃ : Rest scanRegs s s₃ := R.trans ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
    have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, hm]
    have hcx : s₃.gpr .r2 = BitVec.ofNat 32 rest.length := by
      rw [u₃.gpr, u₂.other _ (by decide), e2, ofNat_sub_one (by omega_using []), Nat.add_sub_cancel]
    have hbnd : (scanNext found (rest.length + 1) b).1 < 2 ^ 32 ∧
        ((scanNext found (rest.length + 1) b).1 = 0 → (scanNext found (rest.length + 1) b).2 = 0) := by
      unfold scanNext
      split
      · exact ⟨hl, fun e => by simp only at e; omega⟩
      · exact ⟨h.bound, h.zero⟩
    refine ⟨⟨?_, hcx, by rw [u₃.other _ (by decide), u₂.other _ (by decide)]; exact h3,
      by rw [u₃.other _ (by decide), u₂.other _ (by decide)]; exact h4, ?_, hbnd.1, hbnd.2⟩, ?_, hm₃, R₃⟩
    · rw [u₃.other _ (by decide), u₂.gpr, e1]
    · have := (h.bytes.drop 1 (by simp)).congr hm₃ (by rw [R₃.rd]) (by rw [R₃.wr])
      rw [List.drop_one, List.tail_cons] at this
      exact this
    · rw [z₃, u₂.other _ (by decide), e2, ofNat_sub_one (by omega_using []), Nat.add_sub_cancel, ofNat_beq_zero (by omega_using [hl])]
  have R₁ : Rest scanRegs s s₁ := u₁.rest (by decide)
  have e1 : s₁.gpr .r1 = p := by rw [u₁.other _ (by decide), h.r1]
  have e2 : s₁.gpr .r2 = BitVec.ofNat 32 (rest.length + 1) := by rw [u₁.other _ (by decide), h.r2]; rfl
  refine WP.seq (WP.seq (wp_cmp0 fun s₂ f₂ z₂ => WP.block_nil ?_))
  rw [u₁.other _ (by decide), h.r3, ofNat_beq_zero h.bound] at z₂
  by_cases hf0 : found.1 = 0
  · refine WP.ite true (by rw [eval_eq, z₂]; simp [hf0]) (fun _ => ?_) (fun e => Bool.noConfusion e)
    refine WP.seq (wp_cmp0 fun s₃ f₃ z₃ => WP.block_nil ?_)
    rw [f₂.gpr, u₁.gpr, byte_beq_zero] at z₃
    by_cases hb0 : b = 0
    · refine WP.ite false (by rw [eval_ne, z₃]; simp [hb0]) (fun e => Bool.noConfusion e)
        (fun _ => WP.block_nil ?_)
      have hs : scanNext found (rest.length + 1) b = found := by simp [scanNext, hb0]
      refine after s₃ (by rw [hs, f₃.gpr, f₂.gpr, u₁.other _ (by decide), h.r3])
        (by rw [hs, f₃.gpr, f₂.gpr, u₁.other _ (by decide), h.r4]) (by rw [f₃.mem, f₂.mem, u₁.mem])
        (R₁.trans ((f₂.rest _).trans (f₃.rest _))) (by rw [f₃.gpr, f₂.gpr, e1]) (by rw [f₃.gpr, f₂.gpr, e2])
    · refine WP.ite true (by rw [eval_ne, z₃, decide_eq_false hb0]; rfl)
        (fun _ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_)
        (fun e => Bool.noConfusion e)
      have hs : scanNext found (rest.length + 1) b = (rest.length + 1, b) := by
        simp only [scanNext, hf0, ne_eq, hb0, not_false_eq_true, and_self, ite_true]
      refine after s₅ ?_ ?_ (by rw [u₅.mem, u₄.mem, f₃.mem, f₂.mem, u₁.mem]) ?_ ?_ ?_
      · rw [hs, u₅.other _ (by decide), u₄.gpr, f₃.gpr, f₂.gpr, e2]
      · rw [hs, u₅.gpr, u₄.other _ (by decide), f₃.gpr, f₂.gpr, u₁.gpr]
      · exact R₁.trans ((f₂.rest _).trans ((f₃.rest _).trans ((u₄.rest (by decide)).trans (u₅.rest (by decide)))))
      · rw [u₅.other _ (by decide), u₄.other _ (by decide), f₃.gpr, f₂.gpr, e1]
      · rw [u₅.other _ (by decide), u₄.other _ (by decide), f₃.gpr, f₂.gpr, e2]
  · refine WP.ite false (by rw [eval_eq, z₂]; simp [hf0]) (fun e => Bool.noConfusion e)
      (fun _ => WP.block_nil ?_)
    have hs : scanNext found (rest.length + 1) b = found := by simp [scanNext, hf0]
    exact after s₂ (by rw [hs, f₂.gpr, u₁.other _ (by decide), h.r3])
      (by rw [hs, f₂.gpr, u₁.other _ (by decide), h.r4]) (by rw [f₂.mem, u₁.mem])
      (R₁.trans (f₂.rest _)) (by rw [f₂.gpr, e1]) (by rw [f₂.gpr, e2])

/-- Scan a nonempty q, leading zero padding included. -/
theorem significant_ok {s : State} {p : BitVec 32} {bs : List Byte}
    (h1 : s.gpr .r1 = p) (h2 : s.gpr .r2 = BitVec.ofNat 32 bs.length)
    (hb : BytesIn s p bs) (hn : 0 < bs.length) (h32 : bs.length < 2 ^ 32) :
    WP isa Random.significant s fun t =>
      t.gpr .r3 = BitVec.ofNat 32 (VG.Proof.Dsa.significant bs).1 ∧
      t.gpr .r4 = (VG.Proof.Dsa.significant bs).2.setWidth 32 ∧ t.mem = s.mem ∧ Rest scanRegs s t := by
  unfold Random.significant
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil ?_)
  have R₂ : Rest scanRegs s s₂ := (u₁.rest (by decide)).trans (u₂.rest (by decide))
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have h₀ : ScanState s₂ p bs (0, 0) :=
    ⟨by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact h1,
      by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact h2,
      by rw [u₂.other _ (by decide), u₁.gpr]; rfl, by rw [u₂.gpr]; rfl,
      hb.congr m₂ R₂.rd R₂.wr, by decide, fun _ => rfl⟩
  refine WP.loop (M := isa) (fun n t => ∃ (j : Nat) (found : Nat × Byte), (bs.drop j).length = n ∧ 0 < n ∧
      ScanState t (p + BitVec.ofNat 32 j) (bs.drop j) found ∧
      scanFinish found (bs.drop j) = VG.Proof.Dsa.significant bs ∧
      t.mem = s.mem ∧ Rest scanRegs s t) ?_ bs.length s₂
    ⟨0, (0, 0), by simp, hn, by simpa only [BitVec.add_zero, List.drop_zero] using h₀, by simp [scanFinish],
      m₂, R₂⟩
  rintro n t ⟨j, found, hlen, hpos, ht, htarget, htm, hkt⟩
  obtain ⟨b, rest, hbr⟩ : ∃ b rest, bs.drop j = b :: rest := by
    cases e : bs.drop j with
    | nil => rw [e] at hlen; simp at hlen; omega
    | cons b rest => exact ⟨b, rest, rfl⟩
  rw [hbr] at ht htarget hlen
  have hrl : rest.length + 1 = bs.length - j := by
    have := congrArg List.length hbr; simp only [List.length_drop, List.length_cons] at this; omega_using [this]
  refine WP.mono (significantByte_ok ht (by omega_using [h32, hrl])) fun u ⟨hu, hz, hum, hku⟩ => ?_
  have hrest : bs.drop (j + 1) = rest := by
    rw [← List.drop_drop, hbr, List.drop_one, List.tail_cons]
  have hu' : ScanState u (p + BitVec.ofNat 32 (j + 1)) (bs.drop (j + 1))
      (scanNext found (rest.length + 1) b) := by
    rw [hrest, BitVec.ofNat_add, ← BitVec.add_assoc]; exact hu
  have htarget' := (scanFinish_step found b rest).trans htarget
  have hk := hkt.trans hku
  by_cases he : rest.length = 0
  · left
    have hnil := (congrArg (scanFinish _) (List.length_eq_zero_iff.mp he)).trans (scanFinish_nil hu.zero)
    refine ⟨by rw [eval_ne, hz, he]; rfl, ?_, ?_, hum.trans htm, hk⟩
    · rw [hu.r3, ← hnil.symm.trans htarget']
    · rw [hu.r4, ← hnil.symm.trans htarget']
  · right
    refine ⟨by rw [eval_ne, hz]; simp [he], rest.length, by simp only [List.length_cons] at hlen; omega_using [hlen],
      j + 1, _, by rw [hrest], by omega_using [he], hu', by rw [hrest]; exact htarget', hum.trans htm, hk⟩

end VG.Proof.Dsa.Arm
