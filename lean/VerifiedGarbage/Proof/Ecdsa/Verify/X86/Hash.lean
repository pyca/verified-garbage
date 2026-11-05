module

public import VerifiedGarbage.Impl.Ecdsa.X86.VerifyHash
public import VerifiedGarbage.Proof.Ecdsa.Verify.Hash
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.X86.StackScratch
public import VerifiedGarbage.Proof.Framework.X86.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.Reduce
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Contract
public meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.Ecdsa.X86.VerifyHash

/-!
# ECDSA verification of the hash function's output on x86 (32-bit)

Untrusted: everything here is checked by Lean. `vg_ecdsa_<curve>_verify`
(`Impl/Ecdsa/X86/VerifyHash.lean`) is `hashed` in a frame of `frameBytes`
bytes that copies the five argument slots and passes the buffer at
`esp + bufOff` as a sixth (`withStackScratch`):

* `convert_ok`: `convert len wide` writes `fixedDigest len wide` of the hash
  (`digest`, slot 1; `digest_len`, slot 2) to the first `len` bytes of the
  buffer, changing only the buffer's 80 bytes and `eax`, `ecx`, `edx`
  (`long_ok`, the unrolled copy of the leftmost `len` bytes; `short_ok`: the
  zeros, the copy loop, `copyLoop_ok`, and for P-521 the shift, `shift_ok`).
  It addresses the buffer from `esp`, so it holds of a state whose buffer is
  the frame's, at `esp + bufOff` (`AtBuf`).
* `args_ok`: after `args`, slots 0–3 are `public`, the buffer, `sig` and
  `scratch`, the arguments of the verification that takes the `len` bytes.
* `hashed_correct`: that verification run on narrower permissions
  (`WP.narrowRun`, from `Exec.widen`), then `hashToInt_fixedDigest`.
* `hashed_ct`: `convert` by taint tracking from `τc` (`esp` public, and the
  slots of `digest` and `digest_len`, as public bytes of the argument
  slots), `args` from `esp` alone, and the verification by its own constant
  time (`RelCT.inlineV`).
* `Verified.stackScratchAt`, `Verified.stackScratchAtC`: the frame's theorems
  (`Verified.stackScratchL`, `Verified.stackScratchWipedC`) for code proved
  only from states with the buffer at `esp + 8 + 4 n`, as `narrow` has it
  (`narrow_at`).
* `verifyHash_verified`, `verifyHash_verifiedC` (for a verification that
  reads tables, P-256's comb): `vg_ecdsa_<curve>_verify` under the contract
  of `Spec/`, with `frameBytes` more bytes of stack than the verification;
  `hashSat` its precondition's witness.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86.Hash

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.X86.VerifyHash VG.Impl.StackScratch.X86

/-! ## The conversion -/

/-- The buffer: the sixth argument. -/
abbrev bufB (s : State) : Addr := (arg s 5).setWidth 64

/-- The hash: `digest_len` bytes (the third argument) at `digest` (the second). -/
abbrev digB (s : State) : Addr := (arg s 1).setWidth 64

abbrev hashOf (s : State) : List Byte := Spec.Ecdsa.bytesAt s.mem (digB s) (arg s 2).toNat

/-- What `convert` needs of its state: the buffer at `esp + bufOff`, the
argument slots, the hash readable and the buffer writable, the buffer apart
from them, none wrapping around. -/
structure CPre (len : Nat) (s : State) : Prop where
  len1 : 0 < len
  len66 : len ≤ 66
  buf : (arg s 5).toNat = (s.gpr .esp).toNat + 28
  fitB : (arg s 5).toNat + 80 ≤ 2 ^ 32
  fitD : (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32
  area : (⟨argAddr s 0, 24⟩ : Region) ∈ s.wr
  rd : ∀ i < (arg s 2).toNat, InRegions (s.rd ++ s.wr) (digB s + BitVec.ofNat 64 i) 1
  wr : (⟨bufB s, 80⟩ : Region) ∈ s.wr
  sepD : (⟨bufB s, 80⟩ : Region).Disjoint ⟨digB s, (arg s 2).toNat⟩
  sepA : (⟨bufB s, 80⟩ : Region).Disjoint ⟨argAddr s 0, 24⟩

/-- The buffer's contents and what `convert` changes in memory. -/
structure MPost (len : Nat) (wide : Bool) (s t : State) : Prop where
  buf : ∀ i < len, t.mem (bufB s + BitVec.ofNat 64 i) = (fixedDigest len wide (hashOf s)).getD i 0
  frame : Frame [⟨bufB s, 80⟩] s.mem t.mem

/-- What `convert` leaves: the buffer, and nothing else in memory; every
register but `eax`, `ecx` and `edx` kept. -/
structure CPost (len : Nat) (wide : Bool) (s t : State) : Prop where
  buf : ∀ i < len, t.mem (bufB s + BitVec.ofNat 64 i) = (fixedDigest len wide (hashOf s)).getD i 0
  frame : Frame [⟨bufB s, 80⟩] s.mem t.mem
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

/-! ### Byte loads and stores -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `movzx d, BYTE PTR [b + o]` -/
theorem wp_ldb {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 1)
    (k : ∀ s', Upd s s' d ((s.mem (addr B o)).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d ⟨b, o⟩ :: is)) s Q :=
  cons (s' := s.setReg d _) (by simp only [reduceExec, ea_mk, hb, State.load8, hin, ite_true, Option.map_some])
    (k _ (Upd.setReg _ _ _))

/-- `mov BYTE PTR [b + o], r` -/
theorem wp_stb {b : Reg} {r : Reg8} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hout : InRegions s.wr (addr B o) 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW (addr B o) ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 ⟨b, o⟩ r :: is)) s Q :=
  cons (s' := { s with mem := s.mem.writeW (addr B o) ((s.gpr r.reg).setWidth 8) })
    (by simp only [reduceExec, ea_mk, hb, State.store8, hout, ite_true])
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

end

theorem byte32 (b : Byte) : ((b.setWidth 32).setWidth 8) = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem zero_writeW_apply (m : Mem) (a x : Addr) :
    m.writeW a (0 : BitVec 32) x = if (x - a).toNat < 4 then 0 else m x := by
  simp only [Mem.writeW, Mem.write, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]
  split <;> simp

/-! ### Addresses -/

section
variable {len : Nat} {s : State}

theorem fitE (hp : CPre len s) : (s.gpr .esp).toNat + 108 ≤ 2 ^ 32 := by
  have := hp.buf; have := hp.fitB; omega

theorem addr_esp (hp : CPre len s) {k : Nat} (hk : k < 108) :
    addr (s.gpr .esp) k = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 k :=
  addr_eq (by have := fitE hp; omega)

theorem bufB_eq (hp : CPre len s) : bufB s = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 28 := by
  have h1 := hp.buf
  have h2 := fitE hp
  apply BitVec.eq_of_toNat_eq
  simp only [bufB, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Byte `i` of the buffer, as `[esp + bufOff + i]`. -/
theorem bufAt_eq (hp : CPre len s) {i : Nat} (hi : i < 80) :
    addr (s.gpr .esp) (bufOff + i) = bufB s + BitVec.ofNat 64 i := by
  rw [addr_esp hp (show bufOff + i < 108 by simp only [bufOff, Impl.Ecdsa.X86.VerifyHash.slots]; omega),
    bufB_eq hp, Offset.add_add]
  rfl

theorem argAddr0_eq (hp : CPre len s) : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
  addr_esp hp (k := 4) (by omega)

/-- The slot at `esp + d`, `4 ≤ d ≤ 24`. -/
theorem slot_in (hp : CPre len s) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d ≤ 24) :
    (⟨argAddr s 0, 24⟩ : Region).Contains (addr (s.gpr .esp) d) 4 := by
  rw [argAddr0_eq hp, addr_esp hp (by omega)]
  exact Offset.contains _ h₁ (by omega) (by omega)

theorem slot_rd (hp : CPre len s) {u : State} (hu : u.wr = s.wr) {d : Nat} (h₁ : 4 ≤ d)
    (h₂ : d ≤ 24) : InRegions (u.rd ++ u.wr) (addr (s.gpr .esp) d) 4 :=
  ⟨_, by rw [hu]; exact List.mem_append_right _ hp.area, slot_in hp h₁ h₂⟩

theorem buf_contains {i n : Nat} (h : i + n ≤ 80) :
    (⟨bufB s, 80⟩ : Region).Contains (bufB s + BitVec.ofNat 64 i) n :=
  Offset.contains_base _ h (by omega)

theorem buf_wr (hp : CPre len s) {u : State} (hu : u.wr = s.wr) {i n : Nat} (h : i + n ≤ 80) :
    InRegions u.wr (bufB s + BitVec.ofNat 64 i) n :=
  ⟨_, by rw [hu]; exact hp.wr, buf_contains h⟩

/-- A slot is outside the buffer: memory that differs only in the buffer
holds the same arguments. -/
theorem arg_frame (hp : CPre len s) {m : Mem} (hf : Frame [⟨bufB s, 80⟩] s.mem m) {j : Nat} (hj : j < 6) :
    m.readW (argAddr s j) 32 = arg s j := by
  refine hf.readW (r := ⟨argAddr s 0, 24⟩) (slot_in hp (d := 4 + 4 * j) (by omega) (by omega))
    (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact hp.sepA.symm

/-- A byte of the hash is outside the buffer. -/
theorem dig_frame (hp : CPre len s) {m : Mem} (hf : Frame [⟨bufB s, 80⟩] s.mem m) {i : Nat}
    (hi : i < (arg s 2).toNat) : m (digB s + BitVec.ofNat 64 i) = s.mem (digB s + BitVec.ofNat 64 i) :=
  hf.bytes (R := ⟨digB s, (arg s 2).toNat⟩) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.sepD.symm) (show (arg s 2).toNat ≤ 2 ^ 64 by have := (arg s 2).isLt; omega) hi

theorem dig_addr (hp : CPre len s) {i : Nat} (hi : i < (arg s 2).toNat) :
    addr (arg s 1) i = digB s + BitVec.ofNat 64 i :=
  addr_eq (by have := hp.fitD; omega)

theorem hash_byte {i : Nat} (hi : i < (arg s 2).toNat) :
    (hashOf s).getD i 0 = s.mem (digB s + BitVec.ofNat 64 i) :=
  bytesAt_getD _ _ _ _ hi

/-- A byte of the buffer after a byte store into it. -/
theorem buf_writeW (m : Mem) (b : Byte) {i j : Nat} (hi : i < 80) (hj : j < 80) :
    (m.writeW (bufB s + BitVec.ofNat 64 i) b) (bufB s + BitVec.ofNat 64 j) =
      if j = i then b else m (bufB s + BitVec.ofNat 64 j) := by
  by_cases e : j = i
  · subst e; rw [byte_writeW_eq, ite_eq_left rfl]
  · rw [byte_writeW_ne' _ _ _ (by omega) (by omega) e, ite_eq_right e]

/-- A byte store into the buffer keeps the frame. -/
theorem frame_writeB {m : Mem} (hf : Frame [⟨bufB s, 80⟩] s.mem m) (b : Byte) {i : Nat}
    (hi : i < 80) : Frame [⟨bufB s, 80⟩] s.mem (m.writeW (bufB s + BitVec.ofNat 64 i) b) :=
  hf.writeW (List.mem_singleton_self _) _ (buf_contains (n := 1) (by omega))

end

/-! ### A hash of at least `len` bytes -/

section
variable {len : Nat} {s : State}

/-- After `k` bytes of the copy of the hash's leftmost `len`. -/
structure LInv (s : State) (k : Nat) (u : State) : Prop where
  ecx : u.gpr .ecx = arg s 1
  esp : u.gpr .esp = s.gpr .esp
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  mem : ∀ j < k, u.mem (bufB s + BitVec.ofNat 64 j) = s.mem (digB s + BitVec.ofNat 64 j)
  frame : Frame [⟨bufB s, 80⟩] s.mem u.mem

theorem long_ok (wide : Bool) (hp : CPre len s) {s₁ : State} (he : s₁.gpr .esp = s.gpr .esp)
    (hm : s₁.mem = s.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) (hl : len ≤ (arg s 2).toNat) :
    WP isa (.block (copyLong len)) s₁ (MPost len wide s) := by
  have h66 := hp.len66
  unfold copyLong
  refine wp_ldm he (slot_rd hp hwr (d := 8) (by omega) (by omega)) fun s₂ u₂ => ?_
  have hc : s₂.gpr .ecx = arg s 1 := by rw [u₂.gpr, hm]; rfl
  refine WP.mono (wp_range_flatMap (M := isa) (LInv s) (fun k u hk h => ?_) len (Nat.le_refl _) s₂
    ⟨hc, by rw [u₂.other _ (by decide), he], by rw [u₂.rd, hrd], by rw [u₂.wr, hwr],
      fun j hj => absurd hj (Nat.not_lt_zero _), by rw [u₂.mem, hm]; exact Frame.refl _ _⟩)
    fun t ht => ⟨fun i hi => ?_, ht.frame⟩
  · refine wp_ldb h.ecx (by rw [dig_addr hp (by omega), h.rd, h.wr]; exact hp.rd k (by omega))
      fun u₁ g₁ => ?_
    refine wp_stb (b := .esp) (o := bufOff + k) (by rw [g₁.other _ (by decide), h.esp])
      (by rw [bufAt_eq hp (by omega), g₁.wr]; exact buf_wr hp h.wr (n := 1) (by omega))
      fun u₂ g₂ => WP.block_nil ?_
    have hv : (u₁.gpr Reg8.al.reg).setWidth 8 = s.mem (digB s + BitVec.ofNat 64 k) := by
      rw [show Reg8.al.reg = .eax from rfl, g₁.gpr, byte32, dig_addr hp (by omega),
        dig_frame hp h.frame (by omega)]
    have hm₂ : u₂.mem = u.mem.writeW (bufB s + BitVec.ofNat 64 k) (s.mem (digB s + BitVec.ofNat 64 k)) := by
      rw [g₂.mem, hv, g₁.mem, bufAt_eq hp (by omega)]
    refine ⟨by rw [g₂.gpr, g₁.other _ (by decide), h.ecx], by rw [g₂.gpr, g₁.other _ (by decide), h.esp],
      by rw [g₂.rd, g₁.rd, h.rd], by rw [g₂.wr, g₁.wr, h.wr], fun j hj => ?_, ?_⟩
    · rw [hm₂, buf_writeW _ _ (by omega) (by omega)]
      split
      · rename_i e; subst e; rfl
      · exact h.mem j (by omega)
    · rw [hm₂]; exact frame_writeB h.frame _ (by omega)
  · rw [ht.mem i hi, ← hash_byte (by omega), fixedDigest,
      ite_eq_left_of_eq_true _ _ (eq_true (by rw [length_bytesAt]; exact hl)),
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

end

/-! ### A shorter hash -/

section
variable {len : Nat} {s : State}

/-- After `k` words of zeros. -/
structure ZInv (s : State) (k : Nat) (u : State) : Prop where
  eax : u.gpr .eax = 0
  esp : u.gpr .esp = s.gpr .esp
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  mem : ∀ j < 4 * k, u.mem (bufB s + BitVec.ofNat 64 j) = 0
  frame : Frame [⟨bufB s, 80⟩] s.mem u.mem

theorem zeros_ok (hp : CPre len s) {s₁ : State} (he : s₁.gpr .esp = s.gpr .esp) (hm : s₁.mem = s.mem)
    (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) : WP isa (.block zeros) s₁ (ZInv s 18) := by
  unfold zeros
  refine wp_movi fun s₂ u₂ => ?_
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa) (ZInv s) (fun k u hk h => ?_) 18 (Nat.le_refl _) s₂
    ⟨u₂.gpr, by rw [u₂.other _ (by decide), he], by rw [u₂.rd, hrd], by rw [u₂.wr, hwr],
      fun j hj => absurd hj (Nat.not_lt_zero _), by rw [u₂.mem, hm]; exact Frame.refl _ _⟩
  refine wp_stm (b := .esp) (o := bufOff + 4 * k) h.esp
    (by rw [bufAt_eq hp (by omega)]; exact buf_wr hp h.wr (n := 4) (by omega)) fun u₁ g₁ => WP.block_nil ?_
  have hm₁ : u₁.mem = u.mem.writeW (bufB s + BitVec.ofNat 64 (4 * k)) (0 : BitVec 32) := by
    rw [g₁.mem, h.eax, bufAt_eq hp (by omega)]
  refine ⟨by rw [g₁.gpr, h.eax], by rw [g₁.gpr, h.esp], by rw [g₁.rd, h.rd], by rw [g₁.wr, h.wr],
    fun j hj => ?_, ?_⟩
  · rw [hm₁, zero_writeW_apply, Offset.sub_toNat' _ (by omega) (by omega)]
    by_cases c : 4 * k ≤ j
    · rw [ite_eq_left c]
      split
      · rfl
      · exact h.mem j (by omega)
    · rw [ite_eq_right c, ite_eq_right (by omega)]; exact h.mem j (by omega)
  · rw [hm₁]
    exact h.frame.writeW (List.mem_singleton_self _) _ (buf_contains (n := 4) (by omega))

/-- After `k` bytes of the copy loop: the hash's first `k` bytes after
`len - digest_len` zeros. -/
structure CInv (len : Nat) (s : State) (k : Nat) (u : State) : Prop where
  ecx : u.gpr .ecx = arg s 1 + BitVec.ofNat 32 k
  edx : u.gpr .edx = s.gpr .esp + BitVec.ofNat 32 (bufOff + (len - (arg s 2).toNat + k))
  esp : u.gpr .esp = s.gpr .esp
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  mem : ∀ j < 72, u.mem (bufB s + BitVec.ofNat 64 j) =
    if len - (arg s 2).toNat ≤ j ∧ j < len - (arg s 2).toNat + k then
      s.mem (digB s + BitVec.ofNat 64 (j - (len - (arg s 2).toNat))) else 0
  frame : Frame [⟨bufB s, 80⟩] s.mem u.mem

/-- The buffer holds the zeros and the hash (`tz`). -/
structure TInv (len : Nat) (s : State) (u : State) : Prop where
  esp : u.gpr .esp = s.gpr .esp
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  mem : ∀ j < 72, u.mem (bufB s + BitVec.ofNat 64 j) = tz len (hashOf s) j
  frame : Frame [⟨bufB s, 80⟩] s.mem u.mem

theorem add_ofNat_one (x : BitVec 32) (k : Nat) : x + BitVec.ofNat 32 k + 1 = x + BitVec.ofNat 32 (k + 1) :=
  Offset.add_add x k 1

theorem addr_off (x : BitVec 32) (d : Nat) : addr (x + BitVec.ofNat 32 d) 0 = addr x d := by
  simp only [addr, BitVec.add_zero]

theorem copyLoop_ok (hp : CPre len s) (hl : (arg s 2).toNat < len) (h0 : 0 < (arg s 2).toNat) {u : State}
    (hu : CInv len s 0 u) : WP isa (copyLoop len) u (TInv len s) := by
  have h66 := hp.len66
  have hfD := hp.fitD
  have hE := fitE hp
  refine WP.loop (M := isa) (fun n v => 1 ≤ n ∧ n ≤ (arg s 2).toNat ∧ CInv len s ((arg s 2).toNat - n) v)
    (fun n u ⟨hn1, hnd, h⟩ => ?_) _ u ⟨h0, Nat.le_refl _, by rw [Nat.sub_self]; exact hu⟩
  generalize hk : (arg s 2).toNat - n = k at h
  have hkd : k < (arg s 2).toNat := by omega
  refine wp_ldb (o := 0) h.ecx
    (by rw [addr_off, dig_addr hp hkd, h.rd, h.wr]; exact hp.rd k hkd) fun u₁ g₁ => ?_
  refine wp_stb (o := 0) (b := .edx) (by rw [g₁.other _ (by decide), h.edx])
    (by rw [addr_off, bufAt_eq hp (by omega), g₁.wr]; exact buf_wr hp h.wr (n := 1) (by omega))
    fun u₂ g₂ => ?_
  refine wp_addi fun u₃ g₃ => wp_addi fun u₄ g₄ => wp_mov fun u₅ g₅ => wp_sub fun u₆ g₆ _ => ?_
  refine wp_cmpi fun u₇ f₇ _ z₇ => WP.block_nil ?_
  have hesp₄ : u₄.gpr .esp = s.gpr .esp := by
    rw [g₄.other _ (by decide), g₃.other _ (by decide), g₂.gpr, g₁.other _ (by decide), h.esp]
  have hedx₄ : u₄.gpr .edx = s.gpr .esp + BitVec.ofNat 32 (bufOff + (len - (arg s 2).toNat + (k + 1))) := by
    rw [g₄.gpr, g₃.other _ (by decide), g₂.gpr, g₁.other _ (by decide), h.edx, add_ofNat_one,
      show bufOff + (len - (arg s 2).toNat + k) + 1 = bufOff + (len - (arg s 2).toNat + (k + 1)) by omega]
  have hesp₆ : u₆.gpr .esp = s.gpr .esp := by
    rw [g₆.other _ (by decide), g₅.other _ (by decide), hesp₄]
  have hedx : u₆.gpr .edx = s.gpr .esp + BitVec.ofNat 32 (bufOff + (len - (arg s 2).toNat + (k + 1))) := by
    rw [g₆.other _ (by decide), g₅.other _ (by decide), hedx₄]
  have hecx : u₆.gpr .ecx = arg s 1 + BitVec.ofNat 32 (k + 1) := by
    rw [g₆.other _ (by decide), g₅.other _ (by decide), g₄.other _ (by decide), g₃.gpr, g₂.gpr,
      g₁.other _ (by decide), h.ecx, add_ofNat_one]
  have heax : u₆.gpr .eax = BitVec.ofNat 32 (bufOff + (len - (arg s 2).toNat + (k + 1))) := by
    rw [g₆.gpr, g₅.gpr, g₅.other _ (by decide), hedx₄, hesp₄, Offset.add_sub_cancel_left]
  have hmem : u₇.mem = u.mem.writeW (bufB s + BitVec.ofNat 64 (len - (arg s 2).toNat + k))
      (s.mem (digB s + BitVec.ofNat 64 k)) := by
    rw [f₇.mem, g₆.mem, g₅.mem, g₄.mem, g₃.mem, g₂.mem, show Reg8.al.reg = .eax from rfl, g₁.gpr, byte32,
      g₁.mem, addr_off, bufAt_eq hp (by omega), addr_off, dig_addr hp hkd, dig_frame hp h.frame hkd]
  have hinv : CInv len s (k + 1) u₇ := by
    refine ⟨by rw [f₇.gpr, hecx], by rw [f₇.gpr, hedx], by rw [f₇.gpr, hesp₆],
      by rw [f₇.rd, g₆.rd, g₅.rd, g₄.rd, g₃.rd, g₂.rd, g₁.rd, h.rd],
      by rw [f₇.wr, g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr, h.wr], fun j hj => ?_, ?_⟩
    · rw [hmem, buf_writeW _ _ (by omega) (by omega), h.mem j hj]
      by_cases e : j = len - (arg s 2).toNat + k
      · subst e
        rw [ite_eq_left rfl, ite_eq_left ⟨by omega, by omega⟩,
          show len - (arg s 2).toNat + k - (len - (arg s 2).toNat) = k by omega]
      · rw [ite_eq_right e]
        by_cases c : len - (arg s 2).toNat ≤ j ∧ j < len - (arg s 2).toNat + k
        · rw [ite_eq_left c, ite_eq_left ⟨c.1, by omega⟩]
        · rw [ite_eq_right c, ite_eq_right (by omega)]
    · rw [hmem]; exact frame_writeB h.frame _ (by omega)
  have hz : u₇.zf = some (decide (k + 1 = (arg s 2).toNat)) := by
    rw [z₇, heax, show bufOff = 28 from rfl, Wp.sub_beq (by omega) (by omega)]
    congr 1
    exact decide_eq_decide.mpr ⟨fun e => by omega, fun e => by omega⟩
  by_cases e : k + 1 = (arg s 2).toNat
  · refine .inl ⟨by simp only [eval, hz, e, decide_true, Option.map_some, Bool.not_true], ?_⟩
    refine ⟨by rw [f₇.gpr, hesp₆], hinv.rd, hinv.wr, fun j hj => ?_, hinv.frame⟩
    rw [hinv.mem j hj, tz, length_bytesAt]
    by_cases c : len - (arg s 2).toNat ≤ j ∧ j < len
    · rw [ite_eq_left ⟨c.1, by omega⟩, ite_eq_left c, hash_byte (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right c]
  · refine .inr ⟨by simp only [eval, hz, e, decide_false, Option.map_some, Bool.not_false],
      n - 1, by omega, by omega, by omega, by rw [show (arg s 2).toNat - (n - 1) = k + 1 by omega]; exact hinv⟩

end

/-! ### The shift (P-521) -/

theorem dbl {x : BitVec 32} {a : Nat} (h : x.toNat = a) (ha : 2 * a < 2 ^ 32) : (x + x).toNat = 2 * a := by
  rw [BitVec.toNat_add, h]; omega

/-- The byte `shiftByte` stores: `(b << 7) + (c >> 1)`, low byte. -/
theorem shift_val {x y : BitVec 32} (b c : Byte) (hx : x.toNat = 128 * b.toNat)
    (hy : y = c.setWidth 32 >>> 1) : (x + y).setWidth 8 = sh b c := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  have hc := c.isLt
  rw [sh_toNat, BitVec.toNat_setWidth, BitVec.toNat_add, hx, hy, BitVec.toNat_ushiftRight,
    BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
  omega

theorem shiftByte_eq (i : Nat) : shiftByte i =
    [.movzx8 .eax (bufAt i), .movzx8 .ecx (bufAt (i + 1)), .alu .add .eax (.reg .eax),
      .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
      .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
      .shift .shr .ecx 1, .alu .add .eax (.reg .ecx), .store8 (bufAt i) .al] := rfl

section
variable {len : Nat} {s : State}

/-- After `k` bytes of the shift. -/
structure SInv (len : Nat) (s : State) (k : Nat) (u : State) : Prop where
  esp : u.gpr .esp = s.gpr .esp
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  mem : ∀ j < 72, u.mem (bufB s + BitVec.ofNat 64 j) =
    if j < k then sh (tz len (hashOf s) j) (tz len (hashOf s) (j + 1)) else tz len (hashOf s) j
  frame : Frame [⟨bufB s, 80⟩] s.mem u.mem

theorem buf_rd (hp : CPre len s) {u : State} (hu : u.wr = s.wr) {i : Nat} (hi : i < 80) :
    InRegions (u.rd ++ u.wr) (addr (s.gpr .esp) (bufOff + i)) 1 := by
  rw [bufAt_eq hp hi]; exact inRegions_wr (buf_wr hp hu (n := 1) (by omega))

theorem shift_ok (hp : CPre len s) (hl : (arg s 2).toNat < len) {u : State} (hz : TInv len s u) :
    WP isa (.block (shiftBytes len)) u (MPost len true s) := by
  have h66 := hp.len66
  refine WP.mono (wp_range_flatMap (M := isa) (SInv len s) (fun k u₀ hk h => ?_) len (Nat.le_refl _) u
    ⟨hz.esp, hz.rd, hz.wr, fun j hj => by rw [ite_eq_right (Nat.not_lt_zero _)]; exact hz.mem j hj,
      hz.frame⟩) fun t ht => ⟨fun i hi => ?_, ht.frame⟩
  · rw [shiftByte_eq]
    refine wp_ldb (b := .esp) (o := bufOff + k) h.esp (buf_rd hp h.wr (by omega)) fun u₁ g₁ => ?_
    refine wp_ldb (b := .esp) (o := bufOff + (k + 1)) (by rw [g₁.other _ (by decide), h.esp])
      (by rw [g₁.rd, g₁.wr]; exact buf_rd hp h.wr (by omega)) fun u₂ g₂ => ?_
    refine wp_add fun u₃ g₃ _ => wp_add fun u₄ g₄ _ => wp_add fun u₅ g₅ _ => wp_add fun u₆ g₆ _ => ?_
    refine wp_add fun u₇ g₇ _ => wp_add fun u₈ g₈ _ => wp_add fun u₉ g₉ _ => ?_
    refine wp_shr (by decide) fun u₁₀ g₁₀ _ => wp_add fun u₁₁ g₁₁ _ => ?_
    have hesp : u₁₁.gpr .esp = s.gpr .esp := by
      rw [g₁₁.other _ (by decide), g₁₀.other _ (by decide), g₉.other _ (by decide), g₈.other _ (by decide),
        g₇.other _ (by decide), g₆.other _ (by decide), g₅.other _ (by decide), g₄.other _ (by decide),
        g₃.other _ (by decide), g₂.other _ (by decide), g₁.other _ (by decide), h.esp]
    have hwr : u₁₁.wr = s.wr := by
      rw [g₁₁.wr, g₁₀.wr, g₉.wr, g₈.wr, g₇.wr, g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr, h.wr]
    refine wp_stb (b := .esp) (o := bufOff + k) hesp
      (by rw [bufAt_eq hp (by omega)]; exact buf_wr hp hwr (n := 1) (by omega)) fun u₁₂ g₁₂ => WP.block_nil ?_
    have hb := h.mem k (by omega)
    have hc := h.mem (k + 1) (by omega)
    rw [ite_eq_right (Nat.lt_irrefl _)] at hb
    rw [ite_eq_right (by omega)] at hc
    generalize hB : u₀.mem (bufB s + BitVec.ofNat 64 k) = B at hb
    generalize hC : u₀.mem (bufB s + BitVec.ofNat 64 (k + 1)) = C at hc
    have hBl := B.isLt
    have e₂ : (u₂.gpr .eax).toNat = B.toNat := by
      rw [g₂.other _ (by decide), g₁.gpr, bufAt_eq hp (by omega), hB, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (by omega)]
    have e₃ : (u₃.gpr .eax).toNat = 2 * B.toNat := by rw [g₃.gpr]; exact dbl e₂ (by omega)
    have e₄ : (u₄.gpr .eax).toNat = 2 * (2 * B.toNat) := by rw [g₄.gpr]; exact dbl e₃ (by omega)
    have e₅ : (u₅.gpr .eax).toNat = 2 * (2 * (2 * B.toNat)) := by rw [g₅.gpr]; exact dbl e₄ (by omega)
    have e₆ : (u₆.gpr .eax).toNat = 2 * (2 * (2 * (2 * B.toNat))) := by
      rw [g₆.gpr]; exact dbl e₅ (by omega)
    have e₇ : (u₇.gpr .eax).toNat = 2 * (2 * (2 * (2 * (2 * B.toNat)))) := by
      rw [g₇.gpr]; exact dbl e₆ (by omega)
    have e₈ : (u₈.gpr .eax).toNat = 2 * (2 * (2 * (2 * (2 * (2 * B.toNat))))) := by
      rw [g₈.gpr]; exact dbl e₇ (by omega)
    have e₉ : (u₉.gpr .eax).toNat = 2 * (2 * (2 * (2 * (2 * (2 * (2 * B.toNat)))))) := by
      rw [g₉.gpr]; exact dbl e₈ (by omega)
    have e₁₀ : (u₁₀.gpr .eax).toNat = 128 * B.toNat := by rw [g₁₀.other _ (by decide), e₉]; omega
    have c₁₀ : u₁₀.gpr .ecx = C.setWidth 32 >>> 1 := by
      rw [g₁₀.gpr, g₉.other _ (by decide), g₈.other _ (by decide), g₇.other _ (by decide),
        g₆.other _ (by decide), g₅.other _ (by decide), g₄.other _ (by decide), g₃.other _ (by decide),
        g₂.gpr, g₁.mem, bufAt_eq hp (by omega), hC]
    have hv : (u₁₁.gpr Reg8.al.reg).setWidth 8 = sh B C := by
      rw [show Reg8.al.reg = .eax from rfl, g₁₁.gpr]; exact shift_val B C e₁₀ c₁₀
    have hm : u₁₂.mem = u₀.mem.writeW (bufB s + BitVec.ofNat 64 k) (sh B C) := by
      rw [g₁₂.mem, hv, g₁₁.mem, g₁₀.mem, g₉.mem, g₈.mem, g₇.mem, g₆.mem, g₅.mem, g₄.mem, g₃.mem, g₂.mem,
        g₁.mem, bufAt_eq hp (by omega)]
    refine ⟨by rw [g₁₂.gpr, hesp], by rw [g₁₂.rd, g₁₁.rd, g₁₀.rd, g₉.rd, g₈.rd, g₇.rd, g₆.rd, g₅.rd, g₄.rd,
      g₃.rd, g₂.rd, g₁.rd, h.rd], by rw [g₁₂.wr, hwr], fun j hj => ?_, ?_⟩
    · rw [hm, buf_writeW _ _ (by omega) (by omega)]
      by_cases e : j = k
      · subst e; rw [ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self _), hb, hc]
      · rw [ite_eq_right e, h.mem j hj]
        by_cases c : j < k
        · rw [ite_eq_left c, ite_eq_left (by omega)]
        · rw [ite_eq_right c, ite_eq_right (by omega)]
    · rw [hm]; exact frame_writeB h.frame _ (by omega)
  · rw [ht.mem i (by omega), ite_eq_left hi, fixed_short (by rw [length_bytesAt]; exact hl) true hi]
    rfl

end

/-! ### The cases together -/

section
variable {len : Nat} {s : State}

theorem tail_ok (wide : Bool) (hp : CPre len s) (hl : (arg s 2).toNat < len) {u : State} (hz : TInv len s u) :
    WP isa (.block (if wide then shiftBytes len else [])) u (MPost len wide s) := by
  cases wide with
  | true => exact shift_ok hp hl hz
  | false =>
    refine WP.block_nil ⟨fun i hi => ?_, hz.frame⟩
    rw [hz.mem i (by have := hp.len66; omega), fixed_short (by rw [length_bytesAt]; exact hl) false hi]
    rfl

theorem short_ok (wide : Bool) (hp : CPre len s) {s₁ : State} (he : s₁.gpr .esp = s.gpr .esp)
    (hm : s₁.mem = s.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) (hl : (arg s 2).toNat < len) :
    WP isa (short len wide) s₁ (MPost len wide s) := by
  have h66 := hp.len66
  have hE := fitE hp
  unfold short
  refine WP.seq (WP.block_append (WP.mono (zeros_ok hp he hm hrd hwr) fun u hz => ?_))
  refine wp_ldm hz.esp (slot_rd hp hz.wr (d := 8) (by omega) (by omega)) fun u₁ g₁ => ?_
  refine wp_mov fun u₂ g₂ => wp_addi fun u₃ g₃ => ?_
  refine wp_ldm (b := .esp) (by rw [g₃.other _ (by decide), g₂.other _ (by decide), g₁.other _ (by decide),
    hz.esp]) ?_ fun u₄ g₄ => wp_sub fun u₅ g₅ _ => wp_test fun u₆ f₆ z₆ => WP.block_nil ?_
  · rw [g₃.rd, g₂.rd, g₁.rd, g₃.wr, g₂.wr, g₁.wr]; exact slot_rd hp hz.wr (d := 12) (by omega) (by omega)
  have ha1 : u.mem.readW (addr (s.gpr .esp) 8) 32 = arg s 1 := arg_frame hp hz.frame (j := 1) (by omega)
  have ha2 : u.mem.readW (addr (s.gpr .esp) 12) 32 = arg s 2 := arg_frame hp hz.frame (j := 2) (by omega)
  have heax : u₄.gpr .eax = arg s 2 := by rw [g₄.gpr, g₃.mem, g₂.mem, g₁.mem, ha2]
  have hesp : u₆.gpr .esp = s.gpr .esp := by
    rw [f₆.gpr, g₅.other _ (by decide), g₄.other _ (by decide), g₃.other _ (by decide),
      g₂.other _ (by decide), g₁.other _ (by decide), hz.esp]
  have hecx : u₆.gpr .ecx = arg s 1 := by
    rw [f₆.gpr, g₅.other _ (by decide), g₄.other _ (by decide), g₃.other _ (by decide),
      g₂.other _ (by decide), g₁.gpr, ha1]
  have hedx : u₆.gpr .edx = s.gpr .esp + BitVec.ofNat 32 (bufOff + (len - (arg s 2).toNat + 0)) := by
    rw [f₆.gpr, g₅.gpr, g₄.other _ (by decide), heax, g₃.gpr, g₂.gpr, g₁.other _ (by decide), hz.esp]
    have h2 : arg s 2 = BitVec.ofNat 32 (arg s 2).toNat := ((BitVec.ofNat_toNat 32 _).trans (BitVec.setWidth_eq _)).symm
    conv => lhs; rw [h2]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, Offset.ofNat_sub_ofNat (by omega),
      Nat.add_zero, Nat.add_sub_assoc (Nat.le_of_lt hl)]
  have hmem : u₆.mem = u.mem := by rw [f₆.mem, g₅.mem, g₄.mem, g₃.mem, g₂.mem, g₁.mem]
  have hrd₆ : u₆.rd = s.rd := by rw [f₆.rd, g₅.rd, g₄.rd, g₃.rd, g₂.rd, g₁.rd, hz.rd]
  have hwr₆ : u₆.wr = s.wr := by rw [f₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr, hz.wr]
  have hzb : ∀ j < 72, u₆.mem (bufB s + BitVec.ofNat 64 j) = 0 := fun j hj => by
    rw [hmem]; exact hz.mem j (by omega)
  refine WP.seq (WP.mono (WP.ite (arg s 2 &&& arg s 2 == 0) (by rw [show isa.eval .e u₆ = u₆.zf from rfl, z₆, g₅.other _ (by decide), heax])
    (fun h0 => WP.block_nil ?_) (fun h0 => copyLoop_ok hp hl ?_ ⟨hecx.trans (BitVec.add_zero _).symm, hedx, hesp, hrd₆, hwr₆, fun j hj => ?_, by rw [hmem]; exact hz.frame⟩))
    fun v hv => tail_ok wide hp hl hv)
  · have hd0 : (arg s 2).toNat = 0 := by
      simp only [BitVec.and_self, beq_iff_eq] at h0; rw [h0]; rfl
    refine ⟨hesp, hrd₆, hwr₆, fun j hj => ?_, by rw [hmem]; exact hz.frame⟩
    rw [hzb j hj, tz, length_bytesAt, hd0]
    split
    · simp [Spec.Ecdsa.bytesAt, hd0]
    · rfl
  · simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h0
    exact Nat.pos_of_ne_zero fun e => h0 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
  · rw [hzb j hj, ite_eq_right (by omega)]

theorem convert_mem (wide : Bool) (hp : CPre len s) : WP isa (convert len wide) s (MPost len wide s) := by
  have h66 := hp.len66
  unfold convert
  refine WP.seq (wp_ldm rfl (slot_rd hp rfl (d := 12) (by omega) (by omega)) fun s₁ u₁ => ?_)
  refine wp_cmpi fun s₂ f₂ c₂ _ => WP.block_nil ?_
  have he : s₂.gpr .esp = s.gpr .esp := by rw [f₂.gpr, u₁.other _ (by decide)]
  have hm : s₂.mem = s.mem := by rw [f₂.mem, u₁.mem]
  have hrd : s₂.rd = s.rd := by rw [f₂.rd, u₁.rd]
  have hwr : s₂.wr = s.wr := by rw [f₂.wr, u₁.wr]
  have hc : (s₂.cf = some (decide ((arg s 2).toNat < len))) := by
    rw [c₂, u₁.gpr, Wp.toNat_ofNat_lt (by omega)]; rfl
  refine WP.ite (decide ((arg s 2).toNat < len)) hc (fun h => short_ok wide hp he hm hrd hwr (of_decide_eq_true h))
    (fun h => long_ok wide hp he hm hrd hwr (Nat.le_of_not_lt (of_decide_eq_false h)))

end

/-- `convert` writes only `eax`, `ecx` and `edx`. -/
theorem convert_keep (len : Nat) (wide : Bool) : (instrs (convert len wide)).all (fun i =>
    !(Taint.clobbers i .ebx || Taint.clobbers i .esp || Taint.clobbers i .ebp || Taint.clobbers i .esi ||
      Taint.clobbers i .edi)) = true := by
  cases wide <;>
  simp [instrs, convert, short, copyLong, zeros, copyLoop, shiftBytes, shiftByte, Taint.clobbers,
    Taint.dst, List.all_flatMap, List.all_map]

section
variable {len : Nat} {s : State}

/-- `convert`: the buffer's first `len` bytes are `fixedDigest` of the hash,
and only the buffer and `eax`, `ecx`, `edx` change. -/
theorem convert_ok (wide : Bool) (hp : CPre len s) : WP isa (convert len wide) s (CPost len wide s) := by
  obtain ⟨t, s', he, hq⟩ := convert_mem wide hp
  have hk := convert_keep len wide
  rw [List.all_eq_true] at hk
  refine ⟨t, s', he, hq.buf, hq.frame, fun r h1 h2 h3 => Exec.gpr (fun i hi => ?_) he, (Exec.rdwr he).1,
    (Exec.rdwr he).2, Exec.syms he⟩
  have := hk i hi
  simp only [Bool.not_or, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  obtain ⟨⟨⟨⟨b, sp⟩, bp⟩, si⟩, di⟩ := this
  cases r
  · exact absurd rfl h1
  · exact absurd rfl h2
  · exact absurd rfl h3
  · exact b
  · exact sp
  · exact bp
  · exact si
  · exact di

/-- The slots after `args`: those `core` reads. -/
structure VFacts (s u v : State) : Prop where
  a0 : arg v 0 = arg s 0
  a1 : arg v 1 = arg s 5
  a2 : arg v 2 = arg s 3
  a3 : arg v 3 = arg s 4
  esp : v.gpr .esp = s.gpr .esp
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → v.gpr r = s.gpr r
  mem : Frame [⟨argAddr s 1, 12⟩] u.mem v.mem
  rd : v.rd = s.rd
  wr : v.wr = s.wr
  syms : v.syms = s.syms

theorem slot_wr (hp : CPre len s) {u : State} (hu : u.wr = s.wr) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d ≤ 24) :
    InRegions u.wr (addr (s.gpr .esp) d) 4 :=
  ⟨_, by rw [hu]; exact hp.area, slot_in hp h₁ h₂⟩

theorem slot_sep (hp : CPre len s) {d e : Nat} (h : d + 4 ≤ e ∨ e + 4 ≤ d) (hd : d < 104) (he : e < 104) :
    Mem.Sep (addr (s.gpr .esp) d) (32 / 8) (addr (s.gpr .esp) e) (32 / 8) := by
  rw [addr_esp hp (by omega), addr_esp hp (by omega)]
  exact Offset.sep _ h (by omega) (by omega)

/-- `args`: `core`'s slots. -/
theorem args_ok {wide : Bool} (hp : CPre len s) {u : State} (hu : CPost len wide s u) :
    WP isa (.block args) u (VFacts s u) := by
  have hesp : u.gpr .esp = s.gpr .esp := hu.keep _ (by decide) (by decide) (by decide)
  unfold args
  refine wp_ldm hesp (slot_rd hp hu.wr (d := 24) (by omega) (by omega)) fun u₁ g₁ => ?_
  refine wp_stm (by rw [g₁.other _ (by decide), hesp]) ?_ fun u₂ g₂ => ?_
  · rw [g₁.wr]; exact slot_wr hp hu.wr (d := 8) (by omega) (by omega)
  refine wp_ldm (by rw [g₂.gpr, g₁.other _ (by decide), hesp]) ?_ fun u₃ g₃ => ?_
  · rw [g₂.rd, g₂.wr, g₁.rd, g₁.wr]; exact slot_rd hp hu.wr (d := 16) (by omega) (by omega)
  refine wp_stm (by rw [g₃.other _ (by decide), g₂.gpr, g₁.other _ (by decide), hesp]) ?_ fun u₄ g₄ => ?_
  · rw [g₃.wr, g₂.wr, g₁.wr]; exact slot_wr hp hu.wr (d := 12) (by omega) (by omega)
  refine wp_ldm (by rw [g₄.gpr, g₃.other _ (by decide), g₂.gpr, g₁.other _ (by decide), hesp]) ?_
    fun u₅ g₅ => ?_
  · rw [g₄.rd, g₄.wr, g₃.rd, g₃.wr, g₂.rd, g₂.wr, g₁.rd, g₁.wr]
    exact slot_rd hp hu.wr (d := 20) (by omega) (by omega)
  refine wp_stm (by rw [g₅.other _ (by decide), g₄.gpr, g₃.other _ (by decide), g₂.gpr,
    g₁.other _ (by decide), hesp]) ?_ fun v g₆ => WP.block_nil ?_
  · rw [g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr]; exact slot_wr hp hu.wr (d := 16) (by omega) (by omega)
  have r24 : u.mem.readW (addr (s.gpr .esp) 24) 32 = arg s 5 := arg_frame hp hu.frame (j := 5) (by omega)
  have r16 : u.mem.readW (addr (s.gpr .esp) 16) 32 = arg s 3 := arg_frame hp hu.frame (j := 3) (by omega)
  have r20 : u.mem.readW (addr (s.gpr .esp) 20) 32 = arg s 4 := arg_frame hp hu.frame (j := 4) (by omega)
  have r4 : u.mem.readW (addr (s.gpr .esp) 4) 32 = arg s 0 := arg_frame hp hu.frame (j := 0) (by omega)
  have e1 : u₁.gpr .eax = arg s 5 := by rw [g₁.gpr, r24]
  have m2 : u₂.mem = u.mem.writeW (addr (s.gpr .esp) 8) (arg s 5) := by rw [g₂.mem, e1, g₁.mem]
  have e3 : u₃.gpr .eax = arg s 3 := by
    rw [g₃.gpr, m2, Mem.readW_writeW_sep (slot_sep hp (d := 16) (e := 8) (by omega) (by omega) (by omega))
      (by decide), r16]
  have m4 : u₄.mem = (u.mem.writeW (addr (s.gpr .esp) 8) (arg s 5)).writeW (addr (s.gpr .esp) 12) (arg s 3) := by
    rw [g₄.mem, e3, g₃.mem, m2]
  have e5 : u₅.gpr .eax = arg s 4 := by
    rw [g₅.gpr, m4, Mem.readW_writeW_sep (slot_sep hp (d := 20) (e := 12) (by omega) (by omega) (by omega))
      (by decide), Mem.readW_writeW_sep (slot_sep hp (d := 20) (e := 8) (by omega) (by omega) (by omega))
      (by decide), r20]
  have m6 : v.mem = ((u.mem.writeW (addr (s.gpr .esp) 8) (arg s 5)).writeW (addr (s.gpr .esp) 12)
      (arg s 3)).writeW (addr (s.gpr .esp) 16) (arg s 4) := by
    rw [g₆.mem, e5, g₅.mem, m4]
  have hesp₆ : v.gpr .esp = s.gpr .esp := by
    rw [g₆.gpr, g₅.other _ (by decide), g₄.gpr, g₃.other _ (by decide), g₂.gpr, g₁.other _ (by decide), hesp]
  have harg : ∀ j, arg v j = v.mem.readW (addr (s.gpr .esp) (4 + 4 * j)) 32 := fun j => by
    simp only [arg, argAddr, hesp₆]; rfl
  refine ⟨?_, ?_, ?_, ?_, hesp₆, fun r h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [harg, m6, Mem.readW_writeW_sep (slot_sep hp (d := 4) (e := 16) (by omega) (by omega) (by omega))
      (by decide), Mem.readW_writeW_sep (slot_sep hp (d := 4) (e := 12) (by omega) (by omega) (by omega))
      (by decide), Mem.readW_writeW_sep (slot_sep hp (d := 4) (e := 8) (by omega) (by omega) (by omega))
      (by decide), r4]
  · rw [harg, m6, Mem.readW_writeW_sep (slot_sep hp (d := 8) (e := 16) (by omega) (by omega) (by omega))
      (by decide), Mem.readW_writeW_sep (slot_sep hp (d := 8) (e := 12) (by omega) (by omega) (by omega))
      (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [harg, m6, Mem.readW_writeW_sep (slot_sep hp (d := 12) (e := 16) (by omega) (by omega) (by omega))
      (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [harg, m6]; exact Mem.readW_writeW_self32 _ _ _
  · rw [g₆.gpr, g₅.other _ h1, g₄.gpr, g₃.other _ h1, g₂.gpr, g₁.other _ h1]
    exact hu.keep r h1 h2 h3
  · have hA : ∀ d, 8 ≤ d → d ≤ 16 → (⟨argAddr s 1, 12⟩ : Region).Contains (addr (s.gpr .esp) d) 4 := by
      intro d h₁ h₂
      rw [show argAddr s 1 = addr (s.gpr .esp) 8 from rfl, addr_esp hp (by omega), addr_esp hp (by omega)]
      exact Offset.contains _ h₁ (by omega) (by omega)
    rw [m6]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hA 8 (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (hA 12 (by omega) (by omega))).writeW (List.mem_singleton_self _) _
      (hA 16 (by omega) (by omega))
  · rw [g₆.rd, g₅.rd, g₄.rd, g₃.rd, g₂.rd, g₁.rd, hu.rd]
  · rw [g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr, hu.wr]
  · rw [g₆.syms, g₅.syms, g₄.syms, g₃.syms, g₂.syms, g₁.syms, hu.syms]

end


/-! ## `hashed`, by slot -/

/-- The region of `n` bytes at argument `j`. -/
abbrev R (s : State) (j n : Nat) : Region := ⟨(arg s j).setWidth 64, n⟩

/-- The return address's slot. -/
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩

/-- The `st + 1` bytes below `esp`. -/
abbrev belowR (s : State) (st : Nat) : Region :=
  ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (st + 1), st + 1⟩

/-- The `n` bytes of the argument slots. -/
abbrev areaR (s : State) (n : Nat) : Region := ⟨argAddr s 0, n⟩

/-- Argument `k` is the address `8 + 4 k` bytes above `esp`, as the frame's
`setArgs` passes the buffer. -/
def AtBuf (k : Nat) (s : State) : Prop := (arg s k).toNat = (s.gpr .esp).toNat + (8 + 4 * k)

@[simp] theorem arg_stripConsts (K : List (String × List (BitVec 64))) (s : State) (j : Nat) :
    arg (stripConsts K s) j = arg s j := rfl
@[simp] theorem argAddr_stripConsts (K : List (String × List (BitVec 64))) (s : State) (j : Nat) :
    argAddr (stripConsts K s) j = argAddr s j := rfl

section
variable (I : Spec.Ecdsa.Instance)

/-- `hashed`'s precondition, by slot: `public`, `digest`, `digest_len`,
`sig`, `scratch` and the buffer, the buffer at `esp + bufOff`. -/
structure IPre (st : Nat) (s : State) : Prop where
  stk : st + 1 ≤ (s.gpr .esp).toNat
  fit : (s.gpr .esp).toNat + 4 + 24 ≤ 2 ^ 32
  rd : s.rd = [R s 0 (2 * I.curve.len + 1), R s 1 (arg s 2).toNat, R s 3 (2 * I.curve.len)]
  wr : s.wr = [R s 4 8192, R s 5 80, areaR s 24]
  d04 : (R s 0 (2 * I.curve.len + 1)).Disjoint (R s 4 8192)
  d05 : (R s 0 (2 * I.curve.len + 1)).Disjoint (R s 5 80)
  d0A : (R s 0 (2 * I.curve.len + 1)).Disjoint (areaR s 24)
  d14 : (R s 1 (arg s 2).toNat).Disjoint (R s 4 8192)
  d15 : (R s 1 (arg s 2).toNat).Disjoint (R s 5 80)
  d1A : (R s 1 (arg s 2).toNat).Disjoint (areaR s 24)
  d34 : (R s 3 (2 * I.curve.len)).Disjoint (R s 4 8192)
  d35 : (R s 3 (2 * I.curve.len)).Disjoint (R s 5 80)
  d3A : (R s 3 (2 * I.curve.len)).Disjoint (areaR s 24)
  d45 : (R s 4 8192).Disjoint (R s 5 80)
  d4A : (R s 4 8192).Disjoint (areaR s 24)
  d5A : (R s 5 80).Disjoint (areaR s 24)
  r0 : (retR s).Disjoint (R s 0 (2 * I.curve.len + 1))
  r1 : (retR s).Disjoint (R s 1 (arg s 2).toNat)
  r3 : (retR s).Disjoint (R s 3 (2 * I.curve.len))
  r4 : (retR s).Disjoint (R s 4 8192)
  r5 : (retR s).Disjoint (R s 5 80)
  rA : (retR s).Disjoint (areaR s 24)
  b0 : (belowR s st).Disjoint (R s 0 (2 * I.curve.len + 1))
  b1 : (belowR s st).Disjoint (R s 1 (arg s 2).toNat)
  b3 : (belowR s st).Disjoint (R s 3 (2 * I.curve.len))
  b4 : (belowR s st).Disjoint (R s 4 8192)
  b5 : (belowR s st).Disjoint (R s 5 80)
  bA : (belowR s st).Disjoint (areaR s 24)
  f0 : (arg s 0).toNat + (2 * I.curve.len + 1) ≤ 2 ^ 32
  f1 : (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32
  f3 : (arg s 3).toNat + 2 * I.curve.len ≤ 2 ^ 32
  f4 : (arg s 4).toNat + 8192 ≤ 2 ^ 32
  f5 : (arg s 5).toNat + 80 ≤ 2 ^ 32
  buf : AtBuf 5 s

/-- The facts of the precondition of the verification that takes the `len`
bytes, of `esp` and its slots `public`, the bytes, `sig` and `scratch`. -/
structure KF (st : Nat) (esp p₀ p₁ p₂ p₃ : BitVec 32) (rd wr : List Region) : Prop where
  stk : st + 1 ≤ esp.toNat
  fit : esp.toNat + 4 + 16 ≤ 2 ^ 32
  rd : rd = [⟨p₀.setWidth 64, 2 * I.curve.len + 1⟩, ⟨p₁.setWidth 64, I.curve.len⟩,
    ⟨p₂.setWidth 64, 2 * I.curve.len⟩]
  wr : wr = [⟨p₃.setWidth 64, 8192⟩, ⟨(esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64, 16⟩]
  d03 : (⟨p₀.setWidth 64, 2 * I.curve.len + 1⟩ : Region).Disjoint ⟨p₃.setWidth 64, 8192⟩
  d0A : (⟨p₀.setWidth 64, 2 * I.curve.len + 1⟩ : Region).Disjoint
    ⟨(esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64, 16⟩
  d13 : (⟨p₁.setWidth 64, I.curve.len⟩ : Region).Disjoint ⟨p₃.setWidth 64, 8192⟩
  d1A : (⟨p₁.setWidth 64, I.curve.len⟩ : Region).Disjoint ⟨(esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64, 16⟩
  d23 : (⟨p₂.setWidth 64, 2 * I.curve.len⟩ : Region).Disjoint ⟨p₃.setWidth 64, 8192⟩
  d2A : (⟨p₂.setWidth 64, 2 * I.curve.len⟩ : Region).Disjoint
    ⟨(esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64, 16⟩
  d3A : (⟨p₃.setWidth 64, 8192⟩ : Region).Disjoint ⟨(esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64, 16⟩
  r0 : (⟨esp.setWidth 64, 4⟩ : Region).Disjoint ⟨p₀.setWidth 64, 2 * I.curve.len + 1⟩
  r1 : (⟨esp.setWidth 64, 4⟩ : Region).Disjoint ⟨p₁.setWidth 64, I.curve.len⟩
  r2 : (⟨esp.setWidth 64, 4⟩ : Region).Disjoint ⟨p₂.setWidth 64, 2 * I.curve.len⟩
  r3 : (⟨esp.setWidth 64, 4⟩ : Region).Disjoint ⟨p₃.setWidth 64, 8192⟩
  rA : (⟨esp.setWidth 64, 4⟩ : Region).Disjoint ⟨(esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64, 16⟩
  b0 : (⟨esp.setWidth 64 - BitVec.ofNat 64 (st + 1), st + 1⟩ : Region).Disjoint
    ⟨p₀.setWidth 64, 2 * I.curve.len + 1⟩
  b1 : (⟨esp.setWidth 64 - BitVec.ofNat 64 (st + 1), st + 1⟩ : Region).Disjoint ⟨p₁.setWidth 64, I.curve.len⟩
  b2 : (⟨esp.setWidth 64 - BitVec.ofNat 64 (st + 1), st + 1⟩ : Region).Disjoint
    ⟨p₂.setWidth 64, 2 * I.curve.len⟩
  b3 : (⟨esp.setWidth 64 - BitVec.ofNat 64 (st + 1), st + 1⟩ : Region).Disjoint ⟨p₃.setWidth 64, 8192⟩
  bA : (⟨esp.setWidth 64 - BitVec.ofNat 64 (st + 1), st + 1⟩ : Region).Disjoint
    ⟨(esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64, 16⟩
  f0 : p₀.toNat + (2 * I.curve.len + 1) ≤ 2 ^ 32
  f1 : p₁.toNat + I.curve.len ≤ 2 ^ 32
  f2 : p₂.toNat + 2 * I.curve.len ≤ 2 ^ 32
  f3 : p₃.toNat + 8192 ≤ 2 ^ 32

/-- The precondition of the verification that takes the `len` bytes, by
slot. -/
def KPre (st : Nat) (s : State) : Prop :=
  KF I st (s.gpr .esp) (arg s 0) (arg s 1) (arg s 2) (arg s 3) s.rd s.wr

/-- The verification, of the bytes at `pk`, `e` and `sg`, as the function returns it. -/
abbrev vres (m : Mem) (pk : Addr) (e : Nat) (sg : Addr) : BitVec 32 :=
  if Spec.Ecdsa.verify I.curve (Spec.Ecdsa.bytesAt m pk (2 * I.curve.len + 1)) e
    (Spec.Ecdsa.bytesAt m sg (2 * I.curve.len)) then 1 else 0

/-- What `verifyHashContract` may leak, of a state. -/
abbrev hleakOf (s : State) : List Nat :=
  (Spec.Ecdsa.bytesAt s.mem ((arg s 0).setWidth 64) (2 * I.curve.len + 1) ++ hashOf s ++
    Spec.Ecdsa.bytesAt s.mem ((arg s 3).setWidth 64) (2 * I.curve.len)).map (·.toNat)

/-- What `verifyContract` may leak, of a state. -/
abbrev kleakOf (s : State) : List Nat :=
  (Spec.Ecdsa.bytesAt s.mem ((arg s 0).setWidth 64) (2 * I.curve.len + 1) ++
    Spec.Ecdsa.bytesAt s.mem ((arg s 1).setWidth 64) I.curve.len ++
    Spec.Ecdsa.bytesAt s.mem ((arg s 2).setWidth 64) (2 * I.curve.len)).map (·.toNat)

/-- `hashed`'s contract, by slot, with the tables `K`. -/
def hashR (K : List (String × List (BitVec 64))) (st : Nat) : Contract isa where
  pre s := IPre I st (stripConsts K s) ∧ ConstsOk K (st + 1) s
  post s s' := (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 =
    vres I s.mem ((arg s 0).setWidth 64) (Spec.Ecdsa.hashToInt I.curve (hashOf s)) ((arg s 3).setWidth 64)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ hleakOf (I := I) s₁ = hleakOf (I := I) s₂ ∧
    arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3 ∧
    arg s₁ 4 = arg s₂ 4 ∧ arg s₁ 5 = arg s₂ 5 ∧ ∀ c ∈ K, symAddr s₁ c.1 = symAddr s₂ c.1

/-- The contract of the verification that takes the `len` bytes, by slot. -/
def coreR (K : List (String × List (BitVec 64))) (st : Nat) : Contract isa where
  pre s := KPre I st (stripConsts K s) ∧ ConstsOk K (st + 1) s
  post s s' := (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 =
    vres I s.mem ((arg s 0).setWidth 64)
      (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt s.mem ((arg s 1).setWidth 64) I.curve.len)) ((arg s 2).setWidth 64)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ kleakOf (I := I) s₁ = kleakOf (I := I) s₂ ∧
    arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3 ∧
    ∀ c ∈ K, symAddr s₁ c.1 = symAddr s₂ c.1

end

/-! ## Running the verification on the bytes -/

/-- Verified code run from `s` with narrower permissions: its run from `s`. -/
theorem WP.narrowRun {c : Prog isa} {P : State → Prop} {Q : State → State → Prop}
    (hv : ∀ s, P s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ Q s s') {s : State}
    {rd wr : List Region} (hpre : P (s.withRegions rd wr)) (hc : Covers (rd ++ wr) (s.rd ++ s.wr))
    (hw : Covers wr s.wr) :
    WP isa c s fun s' => abiPreserved (s.withRegions rd wr) s' ∧ Q (s.withRegions rd wr) (s'.withRegions rd wr) := by
  obtain ⟨t, s₁, he, ha, hq⟩ := hv _ hpre
  obtain ⟨hr, hwr⟩ := Exec.rdwr he
  simp only [State.withRegions_rd, State.withRegions_wr] at hr hwr
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at he'
  have e : (s₁.withRegions s.rd s.wr).withRegions rd wr = s₁ := by
    rw [State.withRegions_withRegions, ← hr, ← hwr]; rfl
  exact ⟨t, _, he', ha, by rw [e]; exact hq⟩

/-- Inlined verified code: two runs, from states that narrow to ones its
contract relates, leak the same. -/
theorem RelCT.inlineV {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (s₁.withRegions rd₁ wr₁) ∧ k.pre (s₂.withRegions rd₂ wr₂) ∧
      k.pub (s₁.withRegions rd₁ wr₁) (s₂.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
      Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  obtain ⟨_, n₁⟩ := trace_narrow hv p₁ c₁ w₁ e₁
  obtain ⟨_, n₂⟩ := trace_narrow hv p₂ c₂ w₂ e₂
  exact ⟨hct _ _ _ _ _ _ p₁ p₂ hpub n₁ n₂, trivial⟩

theorem covers_self {r : Region} {rs : List Region} (h : r ∈ rs) :
    ∃ r' ∈ rs, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len :=
  ⟨r, h, 0, by simp, by omega⟩

theorem covers_prefix {B : Addr} {n k : Nat} {rs : List Region} (h : (⟨B, k⟩ : Region) ∈ rs) (hn : n ≤ k) :
    ∃ r' ∈ rs, ∃ off, (⟨B, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧ off + (⟨B, n⟩ : Region).len ≤ r'.len :=
  ⟨_, h, 0, by simp, by simp only; omega⟩

/-! ## The state after the conversion and the moves -/

section
variable {I : Spec.Ecdsa.Instance} {wide : Bool} {K : List (String × List (BitVec 64))} {st : Nat}

theorem length_constRegs (K : List (String × List (BitVec 64))) (s : State) :
    (constRegs K s).length = K.length := by simp [constRegs, Abi.constRegions]

theorem hs_rd {s : State} (hs : (hashR I K st).pre s) :
    s.rd = [R s 0 (2 * I.curve.len + 1), R s 1 (arg s 2).toNat, R s 3 (2 * I.curve.len)] ++ constRegs K s := by
  have e := hs.1.rd
  simp only [stripConsts, State.withRegions_rd, R, arg_withRegions] at e
  rw [← List.take_append_drop (s.rd.length - K.length) s.rd, e, hs.2.1]

theorem cpre_of (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0)
    (h66 : I.curve.len ≤ 66) {s : State} (hs : (hashR I K st).pre s) : CPre I.curve.len s := by
  have hp := hs.1
  have hn := nBits_pos I.curve
  have hwr : s.wr = [R s 4 8192, R s 5 80, areaR s 24] := hp.wr
  have f1 : (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 := hp.f1
  refine ⟨by split at hL <;> omega, h66, hp.buf, hp.f5, f1, by rw [hwr]; simp,
    fun i hi => ⟨R s 1 (arg s 2).toNat, by rw [hs_rd hs]; simp,
      Offset.contains_base _ (by omega) (by omega)⟩, by rw [hwr]; simp, hp.d15.symm, hp.d5A⟩

theorem argAddr_eq {s : State} (h : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32) {j : Nat} (hj : j ≤ 5) :
    argAddr s j = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * j) :=
  addr_eq (by omega)

/-- The slots `core`'s arguments are moved to are within the argument slots. -/
theorem slots_sub {s : State} (h : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32) :
    Region.Sub ⟨argAddr s 1, 12⟩ (areaR s 24) := by
  rw [areaR, argAddr_eq h (j := 1) (by omega), argAddr_eq h (j := 0) (by omega)]
  exact Offset.sub _ (by omega) (by omega)

/-- The verification's readable regions: the key, the `len` bytes, the
signature, and the tables. -/
abbrev rdV (I : Spec.Ecdsa.Instance) (K : List (String × List (BitVec 64))) (s : State) : List Region :=
  [R s 0 (2 * I.curve.len + 1), ⟨bufB s, I.curve.len⟩, R s 3 (2 * I.curve.len)] ++ constRegs K s

/-- Its writable regions: `scratch` and its argument slots. -/
abbrev wrV (s : State) : List Region := [R s 4 8192, areaR s 16]

theorem vpre (h66 : I.curve.len ≤ 66) {s u v : State} (hs : (hashR I K st).pre s)
    (hu : CPost I.curve.len wide s u) (hv : VFacts s u v) :
    (coreR I K st).pre (v.withRegions (rdV I K s) (wrV s)) ∧
      Covers (rdV I K s ++ wrV s) (v.rd ++ v.wr) ∧ Covers (wrV s) v.wr := by
  obtain ⟨hp, hk⟩ := hs
  have hrdS := hs_rd ⟨hp, hk⟩
  have hwr : s.wr = [R s 4 8192, R s 5 80, areaR s 24] := hp.wr
  have hL80 : I.curve.len ≤ 80 := by omega
  have hfit : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.fit
  have hA : argAddr v 0 = argAddr s 0 := by simp only [argAddr, hv.esp]
  have hcR : constRegs K v = constRegs K s := by
    show Abi.constRegions (fun n => (v.syms n).setWidth 64) K = Abi.constRegions (fun n => (s.syms n).setWidth 64) K
    rw [hv.syms]
  have hs16 : Region.Sub (areaR s 16) (areaR s 24) := sub_prefix _ (by omega)
  have hsL : Region.Sub ⟨bufB s, I.curve.len⟩ (R s 5 80) := sub_prefix _ hL80
  have hstrip : stripConsts K (v.withRegions (rdV I K s) (wrV s)) =
      v.withRegions [R s 0 (2 * I.curve.len + 1), ⟨bufB s, I.curve.len⟩, R s 3 (2 * I.curve.len)] (wrV s) := by
    simp only [stripConsts, State.withRegions_rd, State.withRegions_withRegions, State.withRegions_wr, rdV]
    congr 1
    rw [List.length_append, length_constRegs, List.take_left' (by simp)]
  have hsc : R s 4 8192 ∈ s.wr := by rw [hwr]; simp
  have hbf : R s 5 80 ∈ s.wr := by rw [hwr]; simp
  have har : areaR s 24 ∈ s.wr := by rw [hwr]; simp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hstrip]
    show KF I st (v.gpr .esp) (arg v 0) (arg v 1) (arg v 2) (arg v 3) _ _
    rw [hv.esp, hv.a0, hv.a1, hv.a2, hv.a3]
    exact ⟨hp.stk, by have := hp.fit; omega, rfl, rfl, hp.d04, hp.d0A.sub_right hs16,
      hp.d45.symm.sub_left hsL, (hp.d5A.sub_left hsL).sub_right hs16, hp.d34, hp.d3A.sub_right hs16,
      hp.d4A.sub_right hs16, hp.r0, hp.r5.sub_right hsL, hp.r3, hp.r4, hp.rA.sub_right hs16,
      hp.b0, hp.b5.sub_right hsL, hp.b3, hp.b4, hp.bA.sub_right hs16, hp.f0,
      by have : (arg s 5).toNat + 80 ≤ 2 ^ 32 := hp.f5; omega, hp.f3, hp.f4⟩
  · have htab : ∀ t ∈ constRegs K s, t.base.toNat + t.len ≤ 2 ^ abi.ptrBits ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧
        ∀ r ∈ abi.reserved (st + 1) s, t.Disjoint r := hk.2.2.1
    have hres : abi.reserved (st + 1) (v.withRegions (rdV I K s) (wrV s)) = abi.reserved (st + 1) s := by
      simp only [abi, State.withRegions_gpr, hv.esp]
    have hcRw : constRegs K (v.withRegions (rdV I K s) (wrV s)) = constRegs K s := hcR
    refine ⟨?_, ?_, ?_, ?_⟩
    · show ((rdV I K s).drop ((rdV I K s).length - K.length)) = constRegs K (v.withRegions (rdV I K s) (wrV s))
      rw [hcRw]
      simp only [rdV, List.length_append, length_constRegs, List.length_cons, List.length_nil]
      rw [show 0 + 1 + 1 + 1 + K.length - K.length = 3 by omega, List.drop_left' (by simp)]
    · intro c hc i hi
      show v.mem.readW (symAddr v c.1 + BitVec.ofNat 64 (8 * i)) 64 = c.2.getD i 0
      have ht : (⟨symAddr s c.1, 8 * c.2.length⟩ : Region) ∈ constRegs K s :=
        List.mem_map_of_mem (f := fun c => (⟨symAddr s c.1, 8 * c.2.length⟩ : Region)) hc
      have hft : (symAddr s c.1).toNat + 8 * c.2.length ≤ 2 ^ 64 := by
        have := (htab _ ht).1; simp only [abi] at this; omega
      have hcon : (⟨symAddr s c.1, 8 * c.2.length⟩ : Region).Contains
          (symAddr s c.1 + BitVec.ofNat 64 (8 * i)) (64 / 8) :=
        Offset.contains_base _ (by omega) (by omega)
      rw [show symAddr v c.1 = symAddr s c.1 by simp only [symAddr, hv.syms],
        Frame.readW hv.mem hcon (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact ((htab _ ht).2.1 _ har).sub_right (slots_sub hfit)) (by decide),
        Frame.readW hu.frame hcon (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact (htab _ ht).2.1 _ hbf) (by decide)]
      exact hk.2.1 c hc i hi
    · intro t ht
      rw [hcRw] at ht
      obtain ⟨a, b, c⟩ := htab t ht
      refine ⟨a, fun r hr => ?_, fun r hr => c r (by rw [← hres]; exact hr)⟩
      simp only [State.withRegions_wr, wrV, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact b _ hsc
      · exact (b _ har).sub_right hs16
    · intro t ht
      rw [hcRw] at ht
      exact hk.2.2.2 t ht
  · refine Covers.of_sub fun r hr => ?_
    rw [hv.rd, hv.wr]
    simp only [rdV, wrV, List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | rfl | rfl | hr | hr
    · exact covers_self (by rw [hrdS]; simp)
    · exact ⟨_, List.mem_append_right _ hbf, 0, by simp, by simp only; omega⟩
    · exact covers_self (by rw [hrdS]; simp)
    · exact covers_self (by rw [hrdS]; simp [hr])
    · simp only [List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact covers_self (List.mem_append_right _ hsc)
      · exact ⟨_, List.mem_append_right _ har, 0, by simp, by simp only; omega⟩
  · refine Covers.of_sub fun r hr => ?_
    rw [hv.wr]
    simp only [wrV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact covers_self hsc
    · exact ⟨_, har, 0, by simp, by simp only; omega⟩

/-- The memory after the conversion and the moves: the buffer holds the `len`
bytes, the key and the signature are as on entry. -/
theorem vpost (h66 : I.curve.len ≤ 66) {s u v : State} (hs : (hashR I K st).pre s)
    (hu : CPost I.curve.len wide s u) (hv : VFacts s u v) :
    Spec.Ecdsa.bytesAt v.mem (bufB s) I.curve.len = fixedDigest I.curve.len wide (hashOf s) ∧
      Spec.Ecdsa.bytesAt v.mem ((arg s 0).setWidth 64) (2 * I.curve.len + 1) =
        Spec.Ecdsa.bytesAt s.mem ((arg s 0).setWidth 64) (2 * I.curve.len + 1) ∧
      Spec.Ecdsa.bytesAt v.mem ((arg s 3).setWidth 64) (2 * I.curve.len) =
        Spec.Ecdsa.bytesAt s.mem ((arg s 3).setWidth 64) (2 * I.curve.len) := by
  have hp := hs.1
  have hfit : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.fit
  have hf0 : (arg s 0).toNat + (2 * I.curve.len + 1) ≤ 2 ^ 32 := hp.f0
  have hf3 : (arg s 3).toNat + 2 * I.curve.len ≤ 2 ^ 32 := hp.f3
  have dS : ∀ {r : Region}, r.Disjoint (areaR s 24) → r.Disjoint ⟨argAddr s 1, 12⟩ := fun h =>
    h.sub_right (slots_sub hfit)
  refine ⟨bytesAt_ext (length_fixedDigest _ _ _) fun i hi => ?_, ?_, ?_⟩
  · rw [hv.mem.bytes (R := R s 5 80) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dS hp.d5A) (show (80 : Nat) ≤ 2 ^ 64 by decide)
      (show i < 80 by omega)]
    exact hu.buf i hi
  · have d0A : (R s 0 (2 * I.curve.len + 1)).Disjoint (areaR s 24) := hp.d0A
    have d05 : (R s 0 (2 * I.curve.len + 1)).Disjoint (R s 5 80) := hp.d05
    rw [bytesAt_frame hv.mem (dS d0A) (by omega), bytesAt_frame hu.frame d05 (by omega)]
  · have d3A : (R s 3 (2 * I.curve.len)).Disjoint (areaR s 24) := hp.d3A
    have d35 : (R s 3 (2 * I.curve.len)).Disjoint (R s 5 80) := hp.d35
    rw [bytesAt_frame hv.mem (dS d3A) (by omega), bytesAt_frame hu.frame d35 (by omega)]

/-- The return address's slot is apart from what `convert` and `args` write. -/
theorem vret {s u v : State} (hs : (hashR I K st).pre s) (hu : CPost I.curve.len wide s u)
    (hv : VFacts s u v) : v.mem.readW (retR s).base 32 = s.mem.readW (retR s).base 32 := by
  have hp := hs.1
  have hfit : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.fit
  rw [hv.mem.readW (r := retR s) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.rA.sub_right (slots_sub hfit)) (by decide),
    hu.frame.readW (r := retR s) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.r5) (by decide)]

end

theorem hashed_correct {I : Spec.Ecdsa.Instance} {wide : Bool} {K : List (String × List (BitVec 64))}
    {st : Nat} {core : Prog isa}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcv : ∀ s, (coreR I K st).pre s →
      ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ (coreR I K st).post s s')
    (s : State) (hs : (hashR I K st).pre s) :
    ∃ t s', Exec isa (hashed I.curve.len wide core) s t s' ∧ abiPreserved s s' ∧ (hashR I K st).post s s' := by
  have hp := cpre_of hL h66 hs
  have hW : WP isa (hashed I.curve.len wide core) s fun s' => abiPreserved s s' ∧ (hashR I K st).post s s' := by
    unfold hashed
    refine WP.seq (WP.mono (convert_ok wide hp) fun u hu => ?_)
    refine WP.seq (WP.mono (args_ok hp hu) fun v hv => ?_)
    obtain ⟨hpre, hc, hw⟩ := vpre h66 hs hu hv
    refine WP.mono (WP.narrowRun hcv hpre hc hw) fun s' ⟨habi, hpost⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · rw [habi.1 r hr]
      show v.gpr r = s.gpr r
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hv.keep _ (by decide) (by decide) (by decide)
    · have h2 := habi.2
      simp only [State.withRegions_gpr, State.withRegions_mem, hv.esp] at h2
      rw [h2]
      exact vret hs hu hv
    · obtain ⟨e1, e2, e3⟩ := vpost h66 hs hu hv
      have hq := hpost
      simp only [coreR, State.withRegions_gpr, State.withRegions_mem, arg_withRegions, hv.a0, hv.a1,
        hv.a2] at hq
      show (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 =
        vres I s.mem ((arg s 0).setWidth 64) (Spec.Ecdsa.hashToInt I.curve (hashOf s)) ((arg s 3).setWidth 64)
      rw [hq, e1, hashToInt_fixedDigest hL]
      simp only [vres] at e2 e3 ⊢
      rw [e2, e3]
  obtain ⟨t, s', he, ha, hq⟩ := hW
  exact ⟨t, s', he, ha, hq⟩

/-! ## Constant time -/

/-- The taint `convert` is checked from: `esp` public, and the slots of
`digest` and `digest_len` (bytes 4–11 of the argument slots, the third
writable region) public. -/
def τc : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 0, 24], bases := [(.esp, 2, 4)],
    slots := .ofList [(2, 4, 8)] }

/-- The moves of the arguments, from `esp` alone. -/
theorem args_taint : ∃ hc, (taint.check (τr [.esp]) (.block args) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- Byte `k` of the argument slots, `4 ≤ k < 12`: of `digest` or `digest_len`. -/
theorem area_byte {s : State} (hfit : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32) {k : Nat} (h₁ : 4 ≤ k) (h₂ : k < 12) :
    s.mem (argAddr s 0 + BitVec.ofNat 64 k) = (arg s (k / 4)).extractLsb' (8 * (k % 4)) 8 := by
  rw [show argAddr s 0 + BitVec.ofNat 64 k = argAddr s (k / 4) + BitVec.ofNat 64 (k % 4) by
    rw [argAddr_eq hfit (j := 0) (by omega), argAddr_eq hfit (j := k / 4) (by omega), Offset.add_add,
      Offset.add_add]
    congr 2; omega]
  exact Mem.readW_byte _ _ (by omega)

section
variable {I : Spec.Ecdsa.Instance} {wide : Bool} {K : List (String × List (BitVec 64))} {st : Nat}

theorem wf_c {s : State} (hs : (hashR I K st).pre s) : VG.X86.Taint.Wf τc s := by
  have hp := hs.1
  have hwr : s.wr = [R s 4 8192, R s 5 80, areaR s 24] := hp.wr
  have hfit : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.fit
  have hf4 : (arg s 4).toNat + 8192 ≤ 2 ^ 32 := hp.f4
  have hf5 : (arg s 5).toNat + 80 ≤ 2 ^ 32 := hp.f5
  refine Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp' => ?_, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ h => (List.not_mem_nil h).elim⟩
  · rw [hwr]; exact .cons (Nat.zero_le _) (.cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil))
  · rw [hwr]
    refine .cons ?_ (.cons ?_ (.cons (fun _ h => (List.not_mem_nil h).elim) .nil))
    · intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      exacts [hp.d45, hp.d4A]
    · intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb; exact hp.d5A
  · rw [hwr]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · show ((arg s 4).setWidth 64).toNat + 8192 ≤ 2 ^ 32
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (arg s 4).isLt; omega)]; exact hf4
    · show ((arg s 5).setWidth 64).toNat + 80 ≤ 2 ^ 32
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (arg s 5).isLt; omega)]; exact hf5
    · show (argAddr s 0).toNat + 24 ≤ 2 ^ 32
      rw [argAddr_eq hfit (j := 0) (by omega), BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      have := (s.gpr .esp).isLt
      omega
  · simp only [τc, List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'
    show addr (s.gpr .esp) 4 = (Taint.region s 2).base
    rw [Taint.region, hwr]
    rfl

theorem agree_c {s₁ s₂ : State} (h₁ : (hashR I K st).pre s₁) (h₂ : (hashR I K st).pre s₂)
    (hp : (hashR I K st).pub s₁ s₂) : VG.X86.Taint.Agree τc s₁ s₂ := by
  obtain ⟨hsp, -, -, a1, a2, -, a4, a5, -⟩ := hp
  have hwr₁ : s₁.wr = [R s₁ 4 8192, R s₁ 5 80, areaR s₁ 24] := h₁.1.wr
  have hwr₂ : s₂.wr = [R s₂ 4 8192, R s₂ 5 80, areaR s₂ 24] := h₂.1.wr
  have hf₁ : (s₁.gpr .esp).toNat + 28 ≤ 2 ^ 32 := h₁.1.fit
  have hf₂ : (s₂.gpr .esp).toNat + 28 ≤ 2 ^ 32 := h₂.1.fit
  have hA : argAddr s₁ 0 = argAddr s₂ 0 := by simp only [argAddr, hsp]
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf_c h₁, wf_c h₂,
    Taint.slotsOk_of_list rfl (by decide), fun i k hk => ?_, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  · simp only [τc, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hsp
  · rw [hwr₁, hwr₂]; simp only [R, areaR, a4, a5, hA]
  · rw [show τc.slots = Slots.ofList [(2, 4, 8)] from rfl, Slots.has_ofList] at hk
    obtain ⟨sl, hsl, rfl, h₁', h₂'⟩ := hk
    simp only [List.mem_singleton] at hsl
    subst hsl
    simp only at h₁' h₂'
    have e : ∀ s : State, s.wr = [R s 4 8192, R s 5 80, areaR s 24] →
        Taint.byteAddr s 2 k = argAddr s 0 + BitVec.ofNat 64 k := fun s h => by
      rw [Taint.byteAddr, Taint.region, h]; rfl
    rw [e _ hwr₁, e _ hwr₂, area_byte hf₁ h₁' (by omega), area_byte hf₂ h₁' (by omega)]
    rcases (show k / 4 = 1 ∨ k / 4 = 2 by omega) with h | h <;> rw [h]
    · rw [a1]
    · rw [a2]

/-- Two runs as `hashR` relates them. -/
abbrev HP (s₁ s₂ : State) : Prop := (hashR I K st).pre s₁ ∧ (hashR I K st).pre s₂ ∧ (hashR I K st).pub s₁ s₂

theorem core_pub (h66 : I.curve.len ≤ 66) {σ₁ σ₂ x₁ x₂ v₁ v₂ : State} (hp : HP (I := I) (K := K) (st := st) σ₁ σ₂)
    (c₁ : CPost I.curve.len wide σ₁ x₁) (f₁ : VFacts σ₁ x₁ v₁) (c₂ : CPost I.curve.len wide σ₂ x₂)
    (f₂ : VFacts σ₂ x₂ v₂) :
    (coreR I K st).pub (v₁.withRegions (rdV I K σ₁) (wrV σ₁)) (v₂.withRegions (rdV I K σ₂) (wrV σ₂)) := by
  obtain ⟨psp, pl, p0, p1, p2, p3, p4, p5, psy⟩ := hp.2.2
  obtain ⟨b₁, k₁, g₁⟩ := vpost h66 hp.1 c₁ f₁
  obtain ⟨b₂, k₂, g₂⟩ := vpost h66 hp.2.1 c₂ f₂
  obtain ⟨ek, eh, eg⟩ := bytes_of_leak (by simp only [length_bytesAt]) (by simp only [hashOf, length_bytesAt, p2]) pl
  refine ⟨by simp only [State.withRegions_gpr, f₁.esp, f₂.esp, psp], ?_, by simp only [arg_withRegions, f₁.a0, f₂.a0, p0],
    by simp only [arg_withRegions, f₁.a1, f₂.a1, p5], by simp only [arg_withRegions, f₁.a2, f₂.a2, p3],
    by simp only [arg_withRegions, f₁.a3, f₂.a3, p4], fun c hc => ?_⟩
  · simp only [kleakOf, State.withRegions_mem, arg_withRegions, f₁.a0, f₁.a1, f₁.a2, f₂.a0, f₂.a1, f₂.a2]
    rw [b₁, k₁, g₁, b₂, k₂, g₂, ek, eh, eg]
  · show symAddr v₁ c.1 = symAddr v₂ c.1
    simp only [symAddr, f₁.syms, f₂.syms]
    exact psy c hc

theorem hashed_ct {core : Prog isa}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcv : ∀ s, (coreR I K st).pre s →
      ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ (coreR I K st).post s s')
    (hct : ConstantTime isa (coreR I K st).pre (coreR I K st).pub core) {hc : Taint.Hint taint.T}
    (htc : (taint.check τc (convert I.curve.len wide) hc).isSome = true) :
    ConstantTime isa (hashR I K st).pre (hashR I K st).pub (hashed I.curve.len wide core) := by
  obtain ⟨ha, hta⟩ := args_taint
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold hashed
  refine RelCT.seq (R := fun u₁ u₂ => ∃ σ₁ σ₂ x₁ x₂ : State, u₁ = x₁ ∧ u₂ = x₂ ∧
      HP (I := I) (K := K) (st := st) σ₁ σ₂ ∧ CPost I.curve.len wide σ₁ x₁ ∧ CPost I.curve.len wide σ₂ x₂)
    ?_ (RelCT.seq (R := fun v₁ v₂ => ∃ σ₁ σ₂ x₁ x₂ : State, HP (I := I) (K := K) (st := st) σ₁ σ₂ ∧
      CPost I.curve.len wide σ₁ x₁ ∧ VFacts σ₁ x₁ v₁ ∧ CPost I.curve.len wide σ₂ x₂ ∧ VFacts σ₂ x₂ v₂) ?_ ?_)
  · refine ((RelCT.taint (A := taint) τc (fun s₁ s₂ h => agree_c h.1 h.2.1 h.2.2) htc).wpDep
      (F := fun (s t : State) => CPost I.curve.len wide s t) fun s₁ s₂ h =>
        ⟨convert_ok wide (cpre_of hL h66 h.1), convert_ok wide (cpre_of hL h66 h.2.1)⟩).mono (fun _ _ h => h)
      fun t₁ t₂ ⟨_, σ₁, σ₂, hp, a₁, a₂⟩ => ⟨σ₁, σ₂, t₁, t₂, rfl, rfl, hp, a₁, a₂⟩
  · refine RelCT.exists_ fun σ₁ => RelCT.exists_ fun σ₂ => RelCT.exists_ fun x₁ => RelCT.exists_ fun x₂ => ?_
    refine ((RelCT.taint (A := taint) (τr [.esp]) (fun s₁ s₂ h => ?_) hta).wp
      (F₁ := fun v => (HP (I := I) (K := K) (st := st) σ₁ σ₂ ∧ CPost I.curve.len wide σ₁ x₁ ∧
        CPost I.curve.len wide σ₂ x₂) ∧ VFacts σ₁ x₁ v) (F₂ := VFacts σ₂ x₂)
      fun u₁ u₂ ⟨e₁, e₂, hp, c₁, c₂⟩ => by
        subst e₁ e₂
        exact ⟨WP.mono (args_ok (cpre_of hL h66 hp.1) c₁) fun _ h => ⟨⟨hp, c₁, c₂⟩, h⟩,
          args_ok (cpre_of hL h66 hp.2.1) c₂⟩).mono
      (fun _ _ h => h) fun v₁ v₂ ⟨_, ⟨⟨hp, c₁, c₂⟩, f₁⟩, f₂⟩ => ⟨σ₁, σ₂, x₁, x₂, hp, c₁, f₁, c₂, f₂⟩
    obtain ⟨e₁, e₂, hp, c₁, c₂⟩ := h
    subst e₁ e₂
    refine agree_regs fun r hr => ?_
    simp only [List.mem_singleton] at hr
    subst hr
    rw [c₁.keep _ (by decide) (by decide) (by decide), c₂.keep _ (by decide) (by decide) (by decide), hp.2.2.1]
  · refine RelCT.inlineV hcv hct fun v₁ v₂ ⟨σ₁, σ₂, x₁, x₂, hp, c₁, f₁, c₂, f₂⟩ => ?_
    obtain ⟨q₁, cv₁, cw₁⟩ := vpre h66 hp.1 c₁ f₁
    obtain ⟨q₂, cv₂, cw₂⟩ := vpre h66 hp.2.1 c₂ f₂
    exact ⟨_, _, _, _, q₁, q₂, core_pub h66 hp c₁ f₁ c₂ f₂, cv₁, cw₁, cv₂, cw₂⟩

end

/-! ## The contracts of `Spec/`, by slot -/

section
variable {I : Spec.Ecdsa.Instance}

theorem stripConsts_nil (s : State) : stripConsts [] s = s := by
  simp [stripConsts, State.withRegions]

theorem constsOk_nil (st : Nat) (s : State) : ConstsOk [] st s := by
  simp [ConstsOk, constRegs, Abi.constRegions, Abi.constsHeld]

/-- The verification's precondition under `abi`, from `KPre`. -/
theorem core_pre {st : Nat} {s : State} (h : KPre I st s) : (I.verifyContract abi (st + 1)).pre s := by
  have h' : KF I st (s.gpr .esp) (arg s 0) (arg s 1) (arg s 2) (arg s 3) s.rd s.wr := h
  sig_pre [Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig, Spec.Ecdsa.scratchWords,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, stackBelow]
  exact ⟨h'.stk, h'.fit, h'.rd, h'.wr, h'.d03, h'.d0A, h'.d13, h'.d1A, h'.d23, h'.d2A, h'.d3A, h'.r0, h'.r1,
    h'.r2, h'.r3, h'.rA, h'.b0, h'.b1, h'.b2, h'.b3, h'.bA, h'.f0, h'.f1, h'.f2, h'.f3⟩

theorem core_post {st : Nat} {s s' : State} (h : (I.verifyContract abi st).post s s') :
    (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 =
      vres I s.mem ((arg s 0).setWidth 64)
        (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt s.mem ((arg s 1).setWidth 64) I.curve.len))
        ((arg s 2).setWidth 64) := by
  sig_post [Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig, Spec.Ecdsa.scratchWords,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  exact h

theorem core_pub' {st : Nat} {s₁ s₂ : State} (h : s₁.gpr .esp = s₂.gpr .esp ∧ kleakOf (I := I) s₁ = kleakOf (I := I) s₂ ∧
    arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3) :
    (I.verifyContract abi st).pub s₁ s₂ := by
  sig_pub [Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig, Spec.Ecdsa.scratchWords,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  exact h

/-- The verification, run as `coreR` describes it, from its proof under `abi`. -/
theorem coreR_nil {st : Nat} {core : Prog isa} (h : Verified target core (I.verifyContract abi (st + 1))) :
    (∀ s, (coreR I [] st).pre s → ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ (coreR I [] st).post s s') ∧
      ConstantTime isa (coreR I [] st).pre (coreR I [] st).pub core := by
  obtain ⟨hc, hct, -⟩ := h
  have hp : ∀ s, (coreR I [] st).pre s → (I.verifyContract abi (st + 1)).pre s := fun s hs => by
    have := hs.1; rw [stripConsts_nil] at this; exact core_pre this
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_⟩
  · obtain ⟨t, s', he, ha, hq⟩ := hc s (hp s hs)
    exact ⟨t, s', he, ha, core_post hq⟩
  · obtain ⟨psp, pl, p0, p1, p2, p3, -⟩ := hpub
    exact hct _ _ _ _ _ _ (hp _ h₁) (hp _ h₂) (core_pub' ⟨psp, pl, p0, p1, p2, p3⟩) e₁ e₂

/-- The same, from its proof under `abi.withConsts` of its tables. -/
theorem coreR_cons {st : Nat} {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    {core : Prog isa} (h : Verified target core (I.verifyContract (abi.withConsts (c₀ :: cs)) (st + 1))) :
    (∀ s, (coreR I (c₀ :: cs) st).pre s →
      ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ (coreR I (c₀ :: cs) st).post s s') ∧
      ConstantTime isa (coreR I (c₀ :: cs) st).pre (coreR I (c₀ :: cs) st).pub core := by
  obtain ⟨hc, hct, -⟩ := h
  have hp : ∀ s, (coreR I (c₀ :: cs) st).pre s →
      (I.verifyContract (abi.withConsts (c₀ :: cs)) (st + 1)).pre s :=
    fun s hs => pre_consts.mpr ⟨core_pre hs.1, hs.2⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_⟩
  · obtain ⟨t, s', he, ha, hq⟩ := hc s (hp s hs)
    exact ⟨t, s', he, ha, core_post (post_consts.mp hq)⟩
  · obtain ⟨psp, pl, p0, p1, p2, p3, psy⟩ := hpub
    exact hct _ _ _ _ _ _ (hp _ h₁) (hp _ h₂) (pub_consts.mpr ⟨core_pub' ⟨psp, pl, p0, p1, p2, p3⟩, psy⟩) e₁ e₂

/-- `verifyHashContract`'s postcondition. -/
abbrev hPost : I.verifyHashSig.Post abi.ptrBits := fun pk digest digestLen sig _scratch m _m' r =>
  r = if Spec.Ecdsa.verify I.curve (Spec.Ecdsa.bytesAt m pk (2 * I.curve.len + 1))
      (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt m digest digestLen.toNat))
      (Spec.Ecdsa.bytesAt m sig (2 * I.curve.len))
    then 1 else 0

/-- `verifyHashContract`'s leak. -/
abbrev hLeak : Curry (I.verifyHashSig.words abi.ptrBits) (Mem → List Nat) :=
  fun pk digest digestLen sig _scratch m =>
    (Spec.Ecdsa.bytesAt m pk (2 * I.curve.len + 1) ++ Spec.Ecdsa.bytesAt m digest digestLen.toNat ++
      Spec.Ecdsa.bytesAt m sig (2 * I.curve.len)).map (·.toNat)

/-- `hashed`'s contract under `abi`, with the buffer as a last argument. -/
abbrev innerA (st : Nat) : Contract isa :=
  Sig.scratchContract abi I.verifyHashSig "buf" .u8 80 (Curry.const (fun _ => True) _) (hPost (I := I))
    true st (some (hLeak (I := I)))

/-- The same under `abi.withConsts`. -/
abbrev innerK (c₀ : String × List (BitVec 64)) (cs : List (String × List (BitVec 64))) (st : Nat) :
    Contract isa :=
  Sig.scratchContract (abi.withConsts (c₀ :: cs)) I.verifyHashSig "buf" .u8 80
    (Curry.const (fun _ => True) _) (hPost (I := I)) true st (some (hLeak (I := I)))

theorem inner_ipre {st : Nat} {s : State} (h : (innerA (I := I) (st + 1)).pre s) (hb : AtBuf 5 s) :
    IPre I st s := by
  sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Ecdsa.Instance.verifyHashSig,
    Spec.Ecdsa.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, stackBelow] at h
  obtain ⟨stk, fit, rd, wr, d04, d05, d0A, d14, d15, d1A, d34, d35, d3A, d45, d4A, d5A, r0, r1, r3, r4, r5, rA,
    b0, b1, b3, b4, b5, bA, f0, f1, f3, f4, f5⟩ := h
  exact ⟨stk, fit, rd, wr, d04, d05, d0A, d14, d15, d1A, d34, d35, d3A, d45, d4A, d5A, r0, r1, r3, r4, r5, rA,
    b0, b1, b3, b4, b5, bA, f0, f1, f3, f4, f5, hb⟩

theorem inner_post {K : List (String × List (BitVec 64))} {st : Nat} {s s' : State}
    (h : (hashR I K st).post s s') : (innerA (I := I) (st + 1)).post s s' := by
  sig_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, hPost,
    Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  exact h

theorem inner_pub {K : List (String × List (BitVec 64))} {st : Nat} {s₁ s₂ : State}
    (h : (innerA (I := I) (st + 1)).pub s₁ s₂) (hsy : ∀ c ∈ K, symAddr s₁ c.1 = symAddr s₂ c.1) :
    (hashR I K st).pub s₁ s₂ := by
  sig_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, hPost, hLeak, Option.map,
    Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.scratchWords, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] at h
  obtain ⟨psp, pl, p0, p1, p2, p3, p4, p5⟩ := h
  exact ⟨psp, pl, p0, p1, p2, p3, p4, p5, hsy⟩

/-- `hashed` under `abi`, from states with the buffer at `esp + bufOff`. -/
theorem hashed_nil {wide : Bool} {core : Prog isa} {st : Nat}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcore : Verified target core (I.verifyContract abi (st + 1))) {hc : Taint.Hint taint.T}
    (htc : (taint.check τc (convert I.curve.len wide) hc).isSome = true) :
    (∀ s, (innerA (I := I) (st + 1)).pre s → AtBuf 5 s → ∃ t s', Exec isa (hashed I.curve.len wide core) s t s' ∧
      abiPreserved s s' ∧ (innerA (I := I) (st + 1)).post s s') ∧
    ConstantTime isa (fun s => (innerA (I := I) (st + 1)).pre s ∧ AtBuf 5 s) (innerA (I := I) (st + 1)).pub
      (hashed I.curve.len wide core) := by
  obtain ⟨hcv, hct⟩ := coreR_nil hcore
  have hP : ∀ s, (innerA (I := I) (st + 1)).pre s → AtBuf 5 s → (hashR I [] st).pre s := fun s hs hb =>
    ⟨by rw [stripConsts_nil]; exact inner_ipre hs hb, constsOk_nil _ s⟩
  refine ⟨fun s hs hb => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, b₁⟩ ⟨h₂, b₂⟩ hp e₁ e₂ => ?_⟩
  · obtain ⟨t, s', he, ha, hq⟩ := hashed_correct hL h66 hcv s (hP s hs hb)
    exact ⟨t, s', he, ha, inner_post hq⟩
  · exact hashed_ct hL h66 hcv hct htc _ _ _ _ _ _ (hP _ h₁ b₁) (hP _ h₂ b₂)
      (inner_pub hp fun _ h => absurd h List.not_mem_nil) e₁ e₂

/-- `hashed` under `abi.withConsts` of the verification's tables. -/
theorem hashed_cons {wide : Bool} {core : Prog isa} {st : Nat} {c₀ : String × List (BitVec 64)}
    {cs : List (String × List (BitVec 64))}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcore : Verified target core (I.verifyContract (abi.withConsts (c₀ :: cs)) (st + 1)))
    {hc : Taint.Hint taint.T} (htc : (taint.check τc (convert I.curve.len wide) hc).isSome = true) :
    (∀ s, (innerK (I := I) c₀ cs (st + 1)).pre s → AtBuf 5 s →
      ∃ t s', Exec isa (hashed I.curve.len wide core) s t s' ∧
        abiPreserved s s' ∧ (innerK (I := I) c₀ cs (st + 1)).post s s') ∧
    ConstantTime isa (fun s => (innerK (I := I) c₀ cs (st + 1)).pre s ∧ AtBuf 5 s)
      (innerK (I := I) c₀ cs (st + 1)).pub (hashed I.curve.len wide core) := by
  obtain ⟨hcv, hct⟩ := coreR_cons hcore
  have hP : ∀ s, (innerK (I := I) c₀ cs (st + 1)).pre s → AtBuf 5 s → (hashR I (c₀ :: cs) st).pre s :=
    fun s hs hb => by
      obtain ⟨h₁, h₂⟩ := pre_consts.mp hs
      exact ⟨inner_ipre h₁ hb, h₂⟩
  refine ⟨fun s hs hb => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, b₁⟩ ⟨h₂, b₂⟩ hp e₁ e₂ => ?_⟩
  · obtain ⟨t, s', he, ha, hq⟩ := hashed_correct hL h66 hcv s (hP s hs hb)
    exact ⟨t, s', he, ha, post_consts.mpr (inner_post hq)⟩
  · obtain ⟨p₁, p₂⟩ := pub_consts.mp hp
    exact hashed_ct hL h66 hcv hct htc _ _ _ _ _ _ (hP _ h₁ b₁) (hP _ h₂ b₂) (inner_pub p₁ p₂) e₁ e₂

end

/-! ## The frame, with the buffer at `esp + bufOff`

`Verified.stackScratchL` and `Verified.stackScratchWipedC`
(`Proof/Framework/X86/StackScratch.lean`, `StackScratchConsts.lean`) for
code proved only from states whose buffer is the one the frame passes, at
`esp + 8 + 4 n` (`AtBuf`), as `convert` and `args` address it. -/

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- `narrow`'s buffer is at `esp + 8 + 4 n`. -/
theorem narrow_at (hb : 8 + 4 * slots sig + n * e.size ≤ bytes) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    AtBuf (slots sig) (narrow sig e n bytes wa s) := by
  obtain ⟨-, -, -, -, -, -, hlast⟩ := argsState_run hs hb
  obtain ⟨hesp, -⟩ := narrow_facts (nm := "") (e := e) (n := n) hb hs
  have hs' := hs
  rw [pre_stackL] at hs'
  obtain ⟨⟨hst, -⟩, -⟩ := hs'
  unfold AtBuf
  rw [hesp, show arg (narrow sig e n bytes wa s) (slots sig) =
    arg (setArgsState bytes (slots sig) (allocState bytes s)) (slots sig) from rfl, hlast,
    BitVec.toNat_add, BitVec.toNat_ofNat, sub_toNat (by omega)]
  have := (s.gpr .esp).isLt
  rw [Nat.mod_eq_of_lt (a := 8 + 4 * slots sig) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- `Verified.stackScratchL`, for code proved from states with the buffer at
`esp + 8 + 4 k`. -/
theorem Verified.stackScratchAt {c : Prog isa} {k : Nat} (hk : slots sig = k)
    (hcor : ∀ s, (Sig.scratchContract abi sig nm e n pre post wa stack leak).pre s → AtBuf k s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Sig.scratchContract abi sig nm e n pre post wa stack leak).post s s')
    (hct : ConstantTime isa (fun s => (Sig.scratchContract abi sig nm e n pre post wa stack leak).pre s ∧ AtBuf k s)
      (Sig.scratchContract abi sig nm e n pre post wa stack leak).pub c)
    (hb : 8 + 4 * slots sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 4 = 0)
    (hsp : NoSp c) (hd : stackUse c ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hleak : Sig.LeakLocalL abi.ptrBits sig leak) :
    Verified target (withStackScratch bytes k c) (sig.contract abi pre post wa (stack + bytes) leak) := by
  subst hk
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s → ∃ t s₃,
      Exec isa c (narrow sig e n bytes wa s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack leak).post (narrow sig e n bytes wa s) s₃ ∧
      Exec isa (withStackScratch bytes (slots sig) c) s
        (setArgsTrace bytes (s.gpr .esp - BitVec.ofNat 32 bytes) (slots sig) ++ t)
        (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr .eax = s₃.gpr .eax ∧ (popState bytes s s₃).gpr .edx = s₃.gpr .edx := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrow_pre hb.1 hpre hs) (narrow_at hb.1 hs)
    exact ⟨t, s₃, he, hq, withStackScratch_run hb hsp hd hs he ha⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hq, hex, ha, hm, heax, hedx⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_stack]
    have hq' := (post_stack (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)).mp hq
    obtain ⟨-, -, hargs, -⟩ := narrow_facts (nm := nm) (e := e) (n := n) hb.1 hs
    rw [hargs] at hq'
    rw [hm, heax, hedx]
    have hq'' := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params
      post _ _ (stackArgs_length sig s)) _) s₃.mem) _) hq'
    exact hpost _ _ _ _ _ (stackArgs_length sig s) (narrow_agree hb.1 hs)
      (fun r hr x hx => narrow_agreeLists hb.1 hs r ((narrow_lists hb.1 hs) ▸ hr) x hx) hq''
  · obtain ⟨u₁, r₁, f₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, x₂, -⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, (pubL_stackL.mp hp).1.1,
      hct _ _ _ _ _ _ ⟨narrow_pre hb.1 hpre h₁, narrow_at hb.1 h₁⟩ ⟨narrow_pre hb.1 hpre h₂, narrow_at hb.1 h₂⟩
        (narrow_pub hb.1 h₁ h₂ hp hleak) f₁ f₂]

variable {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}

/-- `Verified.stackScratchAt`, under `abi.withConsts` of the code's tables
(`Verified.stackScratchWipedC`, with no words wiped). -/
theorem Verified.stackScratchAtC {c : Prog isa} {k : Nat} (hk : slots sig = k)
    (hcor : ∀ s, (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak).pre s →
      AtBuf k s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧
        (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak).post s s')
    (hct : ConstantTime isa
      (fun s => (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak).pre s ∧ AtBuf k s)
      (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak).pub c)
    (hb : 8 + 4 * slots sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 4 = 0)
    (hsp : NoSp c) (hd : stackUse c ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hsat : ∃ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak) :
    Verified target (withStackScratch bytes k c)
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak) := by
  subst hk
  have hpreL : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂ :=
    fun vs m₁ m₂ hl hb _ => hpre vs m₁ m₂ hl hb
  have hat : ∀ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s →
      AtBuf (slots sig) (narrowC sig e n bytes wa (c₀ :: cs) s) := fun s hs => by
    have h := narrow_at hb.1 (pre_consts.mp hs).1
    simp only [AtBuf, arg, argAddr] at h ⊢
    rw [narrowC_gpr, narrowC_mem]
    exact h
  have hrun : ∀ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s →
      ∃ t s₃, Exec isa c (narrowC sig e n bytes wa (c₀ :: cs) s) t s₃ ∧
      (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak).post
        (narrowC sig e n bytes wa (c₀ :: cs) s) s₃ ∧
      Exec isa (withStackScratch bytes (slots sig) c) s
        (setArgsTrace bytes (s.gpr .esp - BitVec.ofNat 32 bytes) (slots sig) ++ t) (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr .eax = s₃.gpr .eax ∧ (popState bytes s s₃).gpr .edx = s₃.gpr .edx := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrowC_pre hb.1 hpreL hs) (hat s hs)
    exact ⟨t, s₃, he, hq, withStackScratchC_run hb hsp hd hs he ha⟩
  have hpub : ∀ s₁ s₂,
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s₁ →
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s₂ →
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pub s₁ s₂ →
      (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak).pub
        (narrowC sig e n bytes wa (c₀ :: cs) s₁) (narrowC sig e n bytes wa (c₀ :: cs) s₂) := by
    intro s₁ s₂ h₁ h₂ hp
    obtain ⟨hp', hsy⟩ := pub_consts.mp hp
    refine pub_consts.mpr ⟨(pubL_withRegions _ _ _ _).mpr
      (narrow_pub hb.1 (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 ((pubL_withRegions _ _ _ _).mpr hp')
        hleak.toL), ?_⟩
    rw [symAddr_congr (narrowC_syms ..), symAddr_congr (narrowC_syms ..)]
    exact hsy
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hq, hex, ha, hm, heax, hedx⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_consts, post_stack]
    have hq' := (post_stack (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)).mp (post_consts.mp hq)
    obtain ⟨-, -, hargs, -⟩ := narrow_facts (nm := nm) (e := e) (n := n) hb.1 (pre_consts.mp hs).1
    simp only [stackArgs_stripConsts, stripConsts_gpr] at hargs
    rw [stackArgs_narrowC, hargs] at hq'
    rw [hm, heax, hedx]
    have hq'' := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params
      post _ _ (stackArgs_length sig s)) _) s₃.mem) _) hq'
    have hag := narrow_agree (e := e) (n := n) hb.1 (pre_consts.mp hs).1
    simp only [stackArgs_stripConsts, stripConsts_mem] at hag
    rw [narrowC_mem] at hq''
    exact hpost _ _ _ _ _ (stackArgs_length sig s) hag hq''
  · obtain ⟨u₁, _, f₁, _, x₁, _⟩ := hrun s₁ h₁
    obtain ⟨u₂, _, f₂, _, x₂, _⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, ((pubL_stack hl).mp (pub_consts.mp hp).1).1.1,
      hct _ _ _ _ _ _ ⟨narrowC_pre hb.1 hpreL h₁, hat _ h₁⟩ ⟨narrowC_pre hb.1 hpreL h₂, hat _ h₂⟩
        (hpub s₁ s₂ h₁ h₂ hp) f₁ f₂]

end

/-! ## `vg_ecdsa_<curve>_verify` -/

/-- The bytes of a region memories agree on. -/
theorem bytes_local {m₁ m₂ : Mem} {p : Addr} {n N : Nat} (h : ∀ a, (⟨p, N⟩ : Region).Contains a 1 → m₁ a = m₂ a)
    (hn : n ≤ N) : Spec.Ecdsa.bytesAt m₁ p n = Spec.Ecdsa.bytesAt m₂ p n := by
  simp only [Spec.Ecdsa.bytesAt]
  refine List.map_congr_left fun i hi => h _ ?_
  have := List.mem_range.mp hi
  have := Nat.mod_le i (2 ^ 64)
  simp only [Region.Contains]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  omega

section
variable {I : Spec.Ecdsa.Instance}

/-- The key, the hash and the signature, on memories that agree on the
buffers. -/
theorem inputs_local {vs : List (BitVec 64)} {m₁ m₂ : Mem}
    (hlen : vs.length = (I.verifyHashSig.words abi.ptrBits).length)
    (hb : ∀ b ∈ Sig.bufs I.verifyHashSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) :
    ∃ pk dg dl sg sc, vs = [pk, dg, dl, sg, sc] ∧
      Spec.Ecdsa.bytesAt m₁ pk (2 * I.curve.len + 1) = Spec.Ecdsa.bytesAt m₂ pk (2 * I.curve.len + 1) ∧
      Spec.Ecdsa.bytesAt m₁ dg (dl.setWidth 32).toNat = Spec.Ecdsa.bytesAt m₂ dg (dl.setWidth 32).toNat ∧
      Spec.Ecdsa.bytesAt m₁ sg (2 * I.curve.len) = Spec.Ecdsa.bytesAt m₂ sg (2 * I.curve.len) := by
  obtain ⟨pk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dg, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨sg, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.Ecdsa.Instance.verifyHashSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have h₂ : (dl.setWidth 32).toNat ≤ dl.toNat := by rw [BitVec.toNat_setWidth]; exact Nat.mod_le _ _
  exact ⟨pk, dg, dl, sg, sc, rfl, bytes_local hb.1 (Nat.le_refl _), bytes_local hb.2.1 h₂,
    bytes_local hb.2.2.1 (Nat.le_refl _)⟩

theorem post_local : ∀ vs m₁ m₂ m' r, vs.length = (I.verifyHashSig.words abi.ptrBits).length →
    (∀ b ∈ Sig.bufs I.verifyHashSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (I.verifyHashSig.words abi.ptrBits) (hPost (I := I)) vs m₁ m' r →
      Curry.apply (I.verifyHashSig.words abi.ptrBits) (hPost (I := I)) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨pk, dg, dl, sg, sc, rfl, e₁, e₂, e₃⟩ := inputs_local hlen hb
  change r = if Spec.Ecdsa.verify I.curve (Spec.Ecdsa.bytesAt m₁ pk (2 * I.curve.len + 1))
      (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt m₁ dg (dl.setWidth 32).toNat))
      (Spec.Ecdsa.bytesAt m₁ sg (2 * I.curve.len)) then 1 else 0 at h
  change r = if Spec.Ecdsa.verify I.curve (Spec.Ecdsa.bytesAt m₂ pk (2 * I.curve.len + 1))
      (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt m₂ dg (dl.setWidth 32).toNat))
      (Spec.Ecdsa.bytesAt m₂ sg (2 * I.curve.len)) then 1 else 0
  rw [← e₁, ← e₂, ← e₃]
  exact h

theorem leak_local : Sig.LeakLocal abi.ptrBits I.verifyHashSig (some (hLeak (I := I))) := by
  intro vs m₁ m₂ hlen hb
  obtain ⟨pk, dg, dl, sg, sc, rfl, e₁, e₂, e₃⟩ := inputs_local hlen hb
  change (Spec.Ecdsa.bytesAt m₁ pk (2 * I.curve.len + 1) ++ Spec.Ecdsa.bytesAt m₁ dg (dl.setWidth 32).toNat ++
      Spec.Ecdsa.bytesAt m₁ sg (2 * I.curve.len)).map (·.toNat) =
    (Spec.Ecdsa.bytesAt m₂ pk (2 * I.curve.len + 1) ++ Spec.Ecdsa.bytesAt m₂ dg (dl.setWidth 32).toNat ++
      Spec.Ecdsa.bytesAt m₂ sg (2 * I.curve.len)).map (·.toNat)
  rw [e₁, e₂, e₃]

theorem pre_local : ∀ vs (m₁ m₂ : Mem), vs.length = (I.verifyHashSig.words abi.ptrBits).length →
    (∀ b ∈ Sig.bufs I.verifyHashSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (I.verifyHashSig.words abi.ptrBits) (Curry.const (fun _ => True) _) vs m₁ →
      Curry.apply (I.verifyHashSig.words abi.ptrBits) (Curry.const (fun _ => True) _) vs m₂ := by
  intro vs _ _ _ _ _
  rw [Curry.apply_const]
  trivial

theorem slots_eq : X86.slots I.verifyHashSig = Impl.Ecdsa.X86.VerifyHash.slots := by
  simp [X86.slots, X86.widths, Spec.Ecdsa.Instance.verifyHashSig, Sig.words, Param.words, ArgWord.bits,
    abi_ptrBits, Impl.Ecdsa.X86.VerifyHash.slots]

theorem frame_bound : 8 + 4 * X86.slots I.verifyHashSig + 80 * Elem.u8.size ≤ Impl.Ecdsa.X86.VerifyHash.frameBytes ∧
    Impl.Ecdsa.X86.VerifyHash.frameBytes < 4096 ∧ Impl.Ecdsa.X86.VerifyHash.frameBytes % 4 = 0 := by
  rw [slots_eq]; decide

end

/-- `hashed` writes no `esp` if `core` does not. -/
theorem hashed_noSp {len : Nat} {wide : Bool} {core : Prog isa} (h : NoSp core) :
    NoSp (hashed len wide core) := by
  intro i hi
  simp only [hashed, instrs, List.mem_append] at hi
  rcases hi with hi | hi | hi
  · have := List.all_eq_true.mp (convert_keep len wide) i hi
    simp only [Bool.not_or, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
    exact this.1.1.1.2
  · simp only [args, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · exact h i hi

/-- `hashed` uses the stack `core` does. -/
theorem hashed_stackUse {len : Nat} {wide : Bool} {core : Prog isa} {st : Nat} (h : stackUse core ≤ st) :
    stackUse (hashed len wide core) ≤ st := by
  simp only [hashed, convert, short, copyLoop, stackUse, Nat.max_le, Nat.zero_le, and_true, true_and]
  exact h

section
variable {I : Spec.Ecdsa.Instance}

/-- `vg_ecdsa_<curve>_verify` under `abi`, from the verification of the `len`
bytes with `st + 1` bytes of stack: `Impl.Ecdsa.X86.VerifyHash.frameBytes` more. -/
theorem verifyHash_verified {wide : Bool} {core : Prog isa} {st : Nat}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcore : Verified target core (I.verifyContract abi (st + 1))) (hsp : NoSp core)
    (hd : stackUse core ≤ st + 1) {hc : Taint.Hint taint.T}
    (htc : (taint.check τc (convert I.curve.len wide) hc).isSome = true)
    (hsat : ∃ s, (I.verifyHashContract abi (st + 1 + Impl.Ecdsa.X86.VerifyHash.frameBytes)).pre s) :
    Verified target (verifyHash I.curve.len wide core) (I.verifyHashContract abi (st + 1 + Impl.Ecdsa.X86.VerifyHash.frameBytes)) := by
  obtain ⟨hcor, hct⟩ := hashed_nil hL h66 hcore htc
  exact Verified.stackScratchAt (sig := I.verifyHashSig) (nm := "buf") (e := .u8) (n := 80)
    (pre := Curry.const (fun _ => True) _) (post := hPost (I := I)) (wa := true) (stack := st + 1)
    (leak := some (hLeak (I := I))) (bytes := Impl.Ecdsa.X86.VerifyHash.frameBytes) slots_eq hcor hct frame_bound (hashed_noSp hsp)
    (hashed_stackUse hd) (fun vs m₁ m₂ hl hb _ => pre_local vs m₁ m₂ hl hb)
    (fun vs m₁ m₂ m' r hl hb _ => post_local vs m₁ m₂ m' r hl hb) hsat leak_local.toL

/-- `vg_ecdsa_<curve>_verify` under `abi.withConsts`, from the verification of
the `len` bytes with `st + 1` bytes of stack. -/
theorem verifyHash_verifiedC {wide : Bool} {core : Prog isa} {st : Nat} {c₀ : String × List (BitVec 64)}
    {cs : List (String × List (BitVec 64))}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcore : Verified target core (I.verifyContract (abi.withConsts (c₀ :: cs)) (st + 1))) (hsp : NoSp core)
    (hd : stackUse core ≤ st + 1) {hc : Taint.Hint taint.T}
    (htc : (taint.check τc (convert I.curve.len wide) hc).isSome = true)
    (hsat : ∃ s, (I.verifyHashContract (abi.withConsts (c₀ :: cs)) (st + 1 + Impl.Ecdsa.X86.VerifyHash.frameBytes)).pre s) :
    Verified target (verifyHash I.curve.len wide core)
      (I.verifyHashContract (abi.withConsts (c₀ :: cs)) (st + 1 + Impl.Ecdsa.X86.VerifyHash.frameBytes)) := by
  obtain ⟨hcor, hct⟩ := hashed_cons hL h66 hcore htc
  exact Verified.stackScratchAtC (sig := I.verifyHashSig) (nm := "buf") (e := .u8) (n := 80)
    (pre := Curry.const (fun _ => True) _) (post := hPost (I := I)) (wa := true) (stack := st + 1)
    (leak := some (hLeak (I := I))) (bytes := Impl.Ecdsa.X86.VerifyHash.frameBytes) slots_eq hcor hct frame_bound (hashed_noSp hsp)
    (hashed_stackUse hd) pre_local post_local hsat rfl leak_local

end

/-! ## Satisfiability -/

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0x4000, 0x8000` at
`0x20004`. -/
def hashSatMem : Mem := fun a =>
  if a = 0x20005 then 0x10 else if a = 0x20009 then 0x20 else if a = 0x2000d then 0x30 else
  if a = 0x20011 then 0x40 else if a = 0x20015 then 0x80 else 0

/-- A state satisfying `verifyHashContract`'s precondition, for a curve of
`L` bytes: the key at `0x1000`, `0x3000` bytes of hash at `0x2000` (which the
signature at `0x4000`, also read only, may overlap), the scratch space at
`0x8000`. -/
def hashSatState (L : Nat) : State where
  gpr r := match r with
    | .esp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := hashSatMem
  rd := [⟨0x1000, 2 * L + 1⟩, ⟨0x2000, 0x3000⟩, ⟨0x4000, 2 * L⟩]
  wr := [⟨0x8000, 8192⟩, ⟨0x20004, 20⟩]

section
variable {I : Spec.Ecdsa.Instance}

/-- The arguments of `hashSatState`, whatever the curve. -/
theorem hashSat_arg (L j : Nat) : arg (hashSatState L) j = hashSatMem.readW (argAddr (hashSatState 0) j) 32 := rfl

theorem hashSat_a0 : hashSatMem.readW (argAddr (hashSatState 0) 0) 32 = 0x1000 := by decide
theorem hashSat_a1 : hashSatMem.readW (argAddr (hashSatState 0) 1) 32 = 0x2000 := by decide
theorem hashSat_a2 : hashSatMem.readW (argAddr (hashSatState 0) 2) 32 = 0x3000 := by decide
theorem hashSat_a3 : hashSatMem.readW (argAddr (hashSatState 0) 3) 32 = 0x4000 := by decide
theorem hashSat_a4 : hashSatMem.readW (argAddr (hashSatState 0) 4) 32 = 0x8000 := by decide

theorem hashSat_pre (h66 : I.curve.len ≤ 66) {n : Nat} (hn : n + 1 ≤ 0x10000) :
    (I.verifyHashContract abi (n + 1)).pre (hashSatState I.curve.len) := by
  have a0 : arg (hashSatState I.curve.len) 0 = 0x1000 := (hashSat_arg _ _).trans hashSat_a0
  have a1 : arg (hashSatState I.curve.len) 1 = 0x2000 := (hashSat_arg _ _).trans hashSat_a1
  have a2 : arg (hashSatState I.curve.len) 2 = 0x3000 := (hashSat_arg _ _).trans hashSat_a2
  have a3 : arg (hashSatState I.curve.len) 3 = 0x4000 := (hashSat_arg _ _).trans hashSat_a3
  have a4 : arg (hashSatState I.curve.len) 4 = 0x8000 := (hashSat_arg _ _).trans hashSat_a4
  have e : argAddr (hashSatState I.curve.len) 0 = 0x20004 := rfl
  have esp : (hashSatState I.curve.len).gpr .esp = 0x20000 := rfl
  sig_pre [Spec.Ecdsa.Instance.verifyHashContract, Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.scratchWords,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, stackBelow]
  simp only [a0, a1, a2, a3, a4, e]
  simp only [BitVec.reduceSetWidth, BitVec.reduceToNat]
  refine ⟨by omega, by decide, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals first
    | exact Region.disjoint_of_sep (by decide)
    | (apply Region.disjoint_of_le <;> (try simp only [BitVec.reduceToNat]) <;> omega)
    | (refine Region.Disjoint.sub_left ?_ (Offset.sub_below _ (b := 65536) (m := 65536) (by omega) (by omega))
       first
         | exact Region.disjoint_of_sep (by decide)
         | (apply Region.disjoint_of_le <;> (try simp only [BitVec.reduceToNat, BitVec.reduceSub]) <;> omega))
    | omega

/-- `verifyHashContract`'s precondition under `abi` is satisfiable, for up to
64 KiB of stack. -/
theorem hashSat (h66 : I.curve.len ≤ 66) {n : Nat} (hn : n + 1 ≤ 0x10000) :
    ∃ s, (I.verifyHashContract abi (n + 1)).pre s :=
  ⟨_, hashSat_pre h66 hn⟩

end

end VG.Proof.Ecdsa.Verify.X86.Hash
